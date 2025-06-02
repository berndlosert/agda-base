record Foo : Set where
  field foo : String

x : Foo
x =
  let
    y : Foo
    Foo.foo y = "foo"
  in y