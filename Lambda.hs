-- This module requires Generalised Algebraic Data Types (GADTs), which are
-- supported by GHCI (enabled with flag "-XGADTs"). Also, this file is in UTF-8.
module Lambda where

    import Data.List

    -- The type of (lambda) expressions. Note that only single character 
    -- variable identifiers are allowed at the moment.
    data LExpr a where

        -- A variable is an expression made of a single character.
        LVar    :: Char -> LExpr Char

        -- An abstraction is an expression made of a bound variable and an
        -- expression.
        LAbs    :: LExpr Char -> LExpr a -> LExpr a

        -- An application is an expression made of catenating two expressions.
        LApp    :: LExpr a -> LExpr a -> LExpr a

    -- The class "Show" is used for converting lambda expressions into a 
    -- typographical representation. Note that applicative expressions have five
    -- special cases in order to avoid unnecessary parentheses.
    instance Show (LExpr a) where
        -- Single variables can be printed just plainly.
        show (LVar x)               = [x]
        -- Abstraction starts with the lambda ('λ') symbol and has a delimiter
        -- symbol '.' for readability.
        show (LAbs x f)             = "λ" ++ (show x) ++ "." ++ (show f)
        -- This rule is not syntactically necessary, but it makes the 
        -- expressions look more aesthetical (e.g. "(λx.xx)(λx.xx)" vs. 
        -- "(λx.xx)λx.xx").
        show (LApp (LAbs x e) (LAbs y f)) = "(" ++ show (LAbs x e) ++ ")(" ++
                                            show (LAbs y f) ++ ")"
        --
        show (LApp (LAbs x e) (LApp f g)) = "(" ++ show (LAbs x e) ++ ")(" ++ 
                                            show (LApp f g) ++ ")"
        -- Abstraction has no terminator symbol, so applying to abstraction
        -- requires parentheses around abstraction in order to prevent 
        -- ambiguity.
        show (LApp (LAbs x e) f)    = "(" ++ show (LAbs x e) ++ ")" ++ show f
        -- Application is left-associative, so an applicative expression doesn't
        -- need parentheses for disambiguation when there's only a variable on
        -- right-hand side of the applicative expression.
        show (LApp e (LVar y))      = show e ++ show (LVar y)
        -- In this last case, the right-hand side of the applicative expression
        -- is either an abstraction or another application. In both of these
        -- cases, parentheses are required for disambiguation:
        show (LApp e f)             = show e ++ "(" ++ show f ++ ")"

    -- The class "Eq" is used for comparing equality of objects. Note that the
    -- interpretation of equality in lambda calculus is a strictly syntactical
    -- one. For example, (λx.x) equals (λx.x) but not (λy.y) even though we can
    -- clearly see that they behave in an equal fashion.
    instance Eq (LExpr a) where
        (LVar x) == (LVar y)        = x == y
        (LAbs x e) == (LAbs y f)    = x == y && e == f
        (LApp e f) == (LApp g h)    = e == f && g == h 

    -- This helper function is used for convenience. It simply creates an 
    -- expression from a single variable symbol of type Char.
    var     :: Char -> LExpr Char
    var x   = LVar x

    -- This helper function is used for convenience. It simply creates an
    -- abstraction with a bound Char variable and an expression that represents
    -- the body of the expression.
    lam     :: Char -> LExpr a -> LExpr a
    lam x e = LAbs (var x) e

    -- This helper function simply creates an applicative expression from two
    -- expressions.
    app     :: LExpr a -> LExpr a -> LExpr a
    app e f = LApp e f

    -- The following examples are well-known combinators (written here with 
    -- small letters due to Haskell syntax):

    -- The I-combinator corresponds to the identity function in set theory:
    i = lam 'x' $ var 'x' 
    
    -- The K-combinator takes two values and returns the first:
    k = lam 'x' $ lam 'y' $ var 'x'

    -- This is the S-combinator:
    s = lam 'x' $ lam 'y' $ lam 'z' $ 
        (var 'x' `app` var 'z') `app` (var 'y' `app` var 'z')

    -- The Ω-combinator has no β-normal form:
    o = (lam 'x' $ var 'x' `app` var 'x') `app` 
        (lam 'x' $ var 'x' `app` var 'x')

    y = lam 'f' $ (lam 'x' $ var 'f' `app` (var 'x' `app` var 'x')) `app`
        (lam 'x' $ var 'f' `app` (var 'x' `app` var 'x'))

    -- Calculates the list of free variables of an expression.
    free    :: LExpr a -> [LExpr Char]
    free (LVar x)       = [LVar x]
    free (LAbs x e)     = [y | y <- (free e), y /= x]
    free (LApp e f)     = [y | y <- (free e `union` free f)] 

    -- Calculates the list of bound variables of an expression.
    bound   :: LExpr a -> [LExpr Char]
    bound (LVar x)      = []
    bound (LAbs x e)    = x : bound e
    bound (LApp e f)    = [y | y <- (bound e `union` bound f)] 

    -- This binary tree data structure is used for creating parse trees of
    -- expressions.
    data ParseTree a = Nil | 
                        Node {
                            -- This variable is used in the "show" function. It
                            -- is needed for correctly printing the '│' symbols
                            -- in order to have the string representation of
                            -- ParseTree to look good.
                            openParents :: [Bool],
                            -- The expression of the node.
                            expression  :: (LExpr a), 
                            -- List of free variables of the current expression 
                            -- and its subexpressions.
                            freeVars    :: [LExpr Char],
                            -- List of bound variables of the current expression
                            -- and its subexpressions. (Note that a variable can 
                            -- be both free and bound.)
                            boundVars   :: [LExpr Char],
                            -- Left subtree.
                            leftChild   :: (ParseTree a),
                            -- Right subtree.
                            rightChild  :: (ParseTree a)
                        }

    -- This function constructs a parse tree for an expression.
    parse :: [Bool] -> LExpr Char -> ParseTree Char
    parse os (LVar x)   = Node os (LVar x) [] [LVar x] Nil Nil
    parse os (LAbs x e) = Node os (LAbs x e) (free (LAbs x e)) (bound (LAbs x e)) 
                            (parse (os ++ [True]) x) (parse (os ++ [False]) e)
    parse os (LApp e f) = Node os (LApp e f) (free (LApp e f)) (bound (LApp e f)) 
                            (parse (os ++ [True]) e) (parse (os ++ [False]) f)

    -- This is just a shorthand.
--  showTree :: LExpr Char -> ParseTree Char
--  showTree = parse []

    typeof (LVar x)     = " : Var"
    typeof (LAbs x e)   = " : Abs"
    typeof (LApp e f)   = " : App"
    indent2 len | 48 - len > 0  = (iterate (\w -> " " ++ w) "") !! (48 - len)
                | otherwise     = ""
    
    instance Show (ParseTree a) where 
        show (Node os x _ _ Nil Nil) = show x ++ 
                                        indent2 (length (show x) + length os) ++ 
                                        typeof x
        show (Node os x fs bs y z)  = 
                let f = (\(w,m) -> (w ++ (if os !! m then "│" else " "), m+1));
                    indent1 os = fst ((iterate f ("", 0)) !! (length os));
                    terminator (Node _ _ _ _ Nil Nil) = "─ ";
                    terminator _ = "┬ ";
                in (if os == [] then "┌ " else "") ++ show x ++ 
                    indent2 (length (show x) + length os) ++ typeof x ++ 
                    " (ϕ=" ++ show fs ++ ")" ++ "\n" ++ 
                    indent1 os ++ "├" ++ terminator y ++ show y ++ "\n" ++ 
                    indent1 os ++ "└" ++ terminator z ++ show z

{- TODO: Check if Barendregt's rules would be simpler.

    -- Let e be an expression and x a variable. The substitution of x in e with
    -- another expression f is usually denoted as "[f/x]e" in lambda calculus.
    -- When this operation is possible (i.e. there will be no variable capture), 
    -- the result is an expression e' where every free occurence of x has been 
    -- replaced with f. 
    --     This function implements the substution operation with the given 
    -- order of parameters: "sbt <e> <x> <f>" (i.e. first the original 
    -- expression, then the variable to be replaced, and finally the replacement
    -- expression).
    sbt :: LExpr a -> LExpr Char -> LExpr a -> LExpr a
    -- In this first case, the expression e is a LVar y. There will be 
    -- substition if and only if the variable to be replaced, that is x, is the 
    -- same as the only variable of expression e, namely y.
    sbt (LVar y) (LVar x) f     = if x == y then f else (LVar y)
    -- In the second case, e is an expression "λy.g". If x == y, then the bound
    -- variable could be replaced with an expression that is not a variable 
    -- resulting in an incorrect expression. Therefore substitution of the bound
    -- variable cannot be allowed. Additionally either x must not be free in g 
    -- or y must not be free in f in order to prevent variable capture. In this 
    -- case, the substitution operation proceeds recursively.
    sbt (LAbs (LVar y) g) (LVar x) f    = if (x == y || 
                                            (((LVar x) `elem` free g) &&
                                            (LVar y `elem` free f)))
                                    then (LAbs (LVar y) g) 
                                    else (LAbs (LVar y) (sbt g (LVar x) f))

    
-}
