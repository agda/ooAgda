module examplesPaperJFP.triangleRightOperator where

_▹_    :  ∀{A B : Set} → A → (A → B) → B
a ▹ f  =  f a
