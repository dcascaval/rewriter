use egg::*;

define_language! {
  enum GeomLanguage {
      Num(i32),
      "+" = Add([Id; 2]),
      "-" = Sub([Id; 2]),
      "*" = Mul([Id; 2]),
      "/" = Div([Id; 2]),
      "point" = Point([Id; 2]), // Num, Num -> Point
      "line" = Line([Id; 2]), // Point, Point -> Line
      "evaluate" = Evaluate([Id; 2]), // Line, Distance -> Point
      "extrudeline" = ExtrudeLine([Id; 2]), // Line, Depth -> Polygon
      "extrudepoly" = ExtrudePoly([Id; 3]), // Polygon, Line, Depth -> Polygon (line must be on polygon)
      "chamfer" = Chamfer([Id; 3]), // Polygon, Vertex, Radius -> Polygon (vertex must be on polygon)
      "translate" = Translate([Id; 2]), // Element, Vector -> Element (vector is point)
      "scale" = Scale([Id; 3]), // Element, origin, num -> Element (origin is point)
      "let" = Let([Id; 2]), // Symbol, Expr -> let binding
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

}

impl Analysis<GeomLanguage> for GeomAnalysis {
    type Data = GeomData;

    fn make(egraph: &egg::EGraph<GeomLanguage, Self>, enode: &GeomLanguage) -> Self::Data {
        todo!()
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        todo!()
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
     rewrite!("evaluate-pt"; "(evaluate (line (point ?x1 ?y1) (point ?x2 ?y2)) ?t)" =>
          "(point (+ (* ?x2 ?t) (* ?x1 (- 1 ?t)))
                  (+ (* ?y2 ?t) (* ?y1 (- 1 ?t))))"),
  ]
}

pub struct InverseAstSize;
impl<L: Language> CostFunction<L> for InverseAstSize {
  type Cost = i64;
  fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
  where
      C: FnMut(Id) -> Self::Cost,
  {
      enode.fold(0, |sum, id| sum - costs(id))
  }
}


fn run_search(s: &str) -> () {
  let expr = s.parse().unwrap();
  let runner = Runner::<GeomLanguage, GeomAnalysis>::default().with_expr(&expr).run(&make_rules());
  let root = runner.roots[0];

  // Get the biggest one
  let extractor = Extractor::new(&runner.egraph, InverseAstSize);
  let (_, best) = extractor.find_best(root);
  println!("Rewrote {} to {}", expr, best);
}


fn main() {
  run_search("(translate (point 5 5) (point 2 2))");
  println!("Hello, world!");
}
