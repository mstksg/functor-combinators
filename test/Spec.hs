import Test.Tasty
import Tests.HBifunctor
import Tests.HFunctor

main :: IO ()
main =
  defaultMain $
    testGroup
      "Tests"
      [ hfunctorTests
      , hbifunctorTests
      ]
