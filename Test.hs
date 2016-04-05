module Test where

    import Test.QuickCheck
    import Data.List
    import Lambda

    test1 :: LExpr a -> String -> Bool
    test1 x y = show x == y

    main = quickCheck test1 
