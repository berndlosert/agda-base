open import Prelude

record Foo : Type where
  constructor mk
  field unwrap : String

record Bar : Type where
  constructor mk
  field unwrap : String

bar : Bar
bar = mk "bar"

foo : Foo
foo = mk (Bar.unwrap bar)
