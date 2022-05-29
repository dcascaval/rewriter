use egg::*;

define_language! {
  enum GeomLanguage {
      Num(i32),
      "+" = Add([Id; 2]),
      "-" = Sub([Id; 2]),
      "*" = Mul([Id; 2]),
      "/" = Div([Id; 2]), // Rational constructor
      "point" = Point([Id; 2]), // Num, Num -> Point
      "line" = Line([Id; 2]), // Point, Point -> Line
      "evaluate" = Evaluate([Id; 2]), // Line, Distance -> Point
      "extrudeline" = ExtrudeLine([Id; 2]), // Line, Depth -> Polygon
      "extrudepoly" = ExtrudePoly([Id; 3]), // Polygon, Line, Depth -> Polygon (line must be on polygon)
      "chamfer" = Chamfer([Id; 3]), // Polygon, Vertex, Radius -> Polygon (vertex must be on polygon)
      "translate" = Translate([Id; 2]), // Element, Vector -> Element (vector is point)
      "scale" = Scale([Id; 3]), // Element, origin, num -> Element (origin is point)
      "let" = Let([Id; 3]), // let <symbol> = <expr> in <expr>  -> let binding
      Symbol(Symbol),
  }
}

impl GeomLanguage {

    fn num(&self) -> Option<i32> {
        match self {
            GeomLanguage::Num(n) => Some(*n),
            _ => None,
        }
    }

}

type EGraph = egg::EGraph<GeomLanguage, GeomAnalysis>;

#[derive(Default)]
struct GeomAnalysis;

#[derive(Debug)]
struct GeomData {
    constant: Option<(GeomLanguage, PatternAst<GeomLanguage>)>,
}

fn eval(egraph: &EGraph, enode: &GeomLanguage) -> Option<(GeomLanguage, PatternAst<GeomLanguage>)> {
    use GeomLanguage::*;
    let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|c| &c.0);
    match enode {
        Num(n) => Some((enode.clone(), format!("{}", n).parse().unwrap())),
        Add([a, b]) => Some((
            Num(x(a)?.num()? + x(b)?.num()?),
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        Mul([a, b]) => Some((
            Num(x(a)?.num()? * x(b)?.num()?),
            format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        Sub([a, b]) => Some((
            Num(x(a)?.num()? - x(b)?.num()?),
            format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        _ => None,
    }
}

impl Analysis<GeomLanguage> for GeomAnalysis {
    type Data = GeomData;

    fn make(egraph: &egg::EGraph<GeomLanguage, Self>, enode: &GeomLanguage) -> Self::Data {
        let constant = eval(egraph, enode);
        GeomData { constant }
    }

    // Merge State
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        if to.constant.is_none() && from.constant.is_some() {
          to.constant = from.constant;
          DidMerge(true, false)
        } else {
          DidMerge(false, true)
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            let const_id = egraph.add(c.0);
            egraph.union(id, const_id);
        }
    }
}

fn make_rules() -> Vec<Rewrite<GeomLanguage, GeomAnalysis>> {
    vec![
        // These are all useful to us to generally widen the space but won't directly be responsible for much
        // since they are _actually_ equivalent for all a,b instead of fake-equivalent for some constants.
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        rewrite!("sub-0"; "(- ?a 0)" => "?a"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("mul-1"; "(* ?a 1)" => "?a"),
        rewrite!("div-1"; "(/ ?a 1)" => "?a"),
        rewrite!("div-0"; "(/ 0 ?a)" => "0"),
        rewrite!("div-self"; "(/ ?a ?a)" => "1"),

        // These start to be more useful as it allows the incorporation of these nodes into the graph
        rewrite!("evaluate-0"; "(evaluate (line ?a ?b) 0)" => "?a"),
        rewrite!("evaluate-1"; "(evaluate (line ?a ?b) 1)" => "?b"),
        rewrite!("translate-0"; "(translate ?a (point 0 0))" => "?a"),
        rewrite!("scale-1"; "(scale ?a ?b 1)" => "?a"),
        rewrite!("extrudepoly-0"; "(extrudepoly ?p ?l 0)" => "?p"),
        rewrite!("chamfer-0"; "(chamfer ?p ?v 0)" => "?p"),
        // And at this point we're basically giving an interpereter to decompose expressions
        rewrite!("translate-pt"; "(translate (point ?x ?y) (point ?dx ?dy))" => "(point (+ ?x ?dx) (+ ?y ?dy))"),
        rewrite!("translate-ln"; "(translate (line ?a ?b) ?v)" => "(line (translate ?a ?v) (translate ?b ?v))"),
        rewrite!("evaluate-pt"; "(evaluate (line (point ?x1 ?y1) (point ?x2 ?y2)) (/ ?t0 ?t1))" =>
          "(point (+ (/ (* ?x2 ?t0) ?t1) (/ (* ?x1 (- 1 ?t0)) ?t1))
                  (+ (/ (* ?y2 ?t0) ?t1) (/ (* ?y1 (- 1 ?t0)) ?t1)))"), // evaluating the division would just round to 0
    ]
}

pub struct ParametrizationCost;

impl CostFunction<GeomLanguage> for ParametrizationCost {
    type Cost = i64;
    fn cost<C>(&mut self, enode: &GeomLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
          GeomLanguage::Num(n) => if *n != 1 { 1 } else {0},
          GeomLanguage::Add(_) => 0,
          _ => 10
        };
        enode.fold(op_cost, |sum,id| sum + costs(id))
    }
}

fn run_search<Cost : CostFunction<GeomLanguage>>(s: &str, cost: Cost) -> () {
    let expr = s.parse().unwrap();
    let runner = Runner::<GeomLanguage, GeomAnalysis>::default()
        .with_expr(&expr)
        .run(&make_rules());
    let root = runner.roots[0];

    // Get the biggest one
    let extractor = Extractor::new(&runner.egraph, cost);
    let (_, best) = extractor.find_best(root);
    println!("Rewrote {} to {}", expr, best);
}

fn main() {
    run_search("(translate (point 5 5) (point 2 2))", AstSize);
    run_search("(evaluate (line (point 0 0) (point 10 10)) (/ 1 10))", AstSize);
    run_search( "4", ParametrizationCost)
}
