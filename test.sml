fun test {x, y=10, ...} = 10
  | test {x, y=_, ...} = 12;

val _ = test {x=10, y=12};
