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
      Let(Symbol, [Id; 1]),
      Symbol(Symbol),
  }
}

fn make_rules() -> Vec<Rewrite<GeomLanguage, ()>> {
  // These are all useful to us to generally widen the space but won't directly be responsible for much
  // since they are _actually_ equivalent for all a,b instead of fake-equivalent for some constants.
  vec![
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
      rewrite!("chamfer-0"; "(chamfer ?p ?v 0)" => "?p")
  ]
}



fn main() {

  println!("Hello, world!");
}
