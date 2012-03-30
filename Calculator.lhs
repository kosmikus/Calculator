> import Control.Applicative
> import Control.Monad.State
> import Data.Char hiding (isSymbol)
> import Data.List as L
> import Data.Map as M
> import Data.Maybe
> import Test.HUnit

Lexing
======

We need a datatype to hold tokens:

> data Token =
>     Ident  String     -- ^ identifier
>   | Number Double     -- ^ numeric literal
>   | Symbol Char       -- ^ symbol / operator character
>   | LPar              -- ^ opening parenthesis
>   | RPar              -- ^ closing parenthesis
>   | Err    Char       -- ^ unknown token
>   deriving (Show, Eq)

We will also need a number of simple helpers that check if a given token
belongs to a certain category, and extract the value from it if it does.

> toNumber :: Token -> Maybe Double
> toNumber (Number n) = Just n
> toNumber _          = Nothing

> toIdent :: Token -> Maybe String
> toIdent (Ident x) = Just x
> toIdent _         = Nothing

For symbols, we will always know which symbol we expect, therefore we pass the
expected symbol and check if the symbol in the token matches. We use 'Maybe ()'
instead of 'Bool' here as the result type so that the function is
type-compatible with the 'toNumber' and 'toIndent' functions above.

> isSymbol :: Char -> Token -> Maybe ()
> isSymbol s (Symbol c) | s == c = Just ()
> isSymbol _ _                   = Nothing

The 'LPar' and 'RPar' tokens don't have any payload. Again, we use
'()' in these cases.

> toLPar :: Token -> Maybe ()
> toLPar LPar = Just ()
> toLPar _    = Nothing

> toRPar :: Token -> Maybe ()
> toRPar RPar = Just ()
> toRPar _    = Nothing


After these preparations, we can tackle lexing. As we have a constructor for
unknown tokens, lexing cannot fail. We take the input string and produce a list
of tokens. Lexing is in essence a hand-written finite state machine. We look at
the current character of the input. If this is a single-character token, we
produce it immediately and continue. If it is a space, we drop it. If it is the
start of an identifier or a number, we switch to a different state by calling
'lexIdent' or 'lexNumber'.

> tokenize :: String -> [Token]
> tokenize []                = []
> tokenize (x : xs)
>   | x == '('               = LPar : tokenize xs
>   | x == ')'               = RPar : tokenize xs
>   | isSpace x              = tokenize xs
>   | isOpSymbol x           = Symbol x : tokenize xs
>   | isLetter x             = lexIdent  x xs
>   | isNumber x             = lexNumber x xs
>   | otherwise              = Err x : tokenize xs

The function 'isOpSymbol' tests if a character is a valid operator symbol.
We could already parse the operator here, but decide to defer that to the
actual parsing stage.

> isOpSymbol :: Char -> Bool
> isOpSymbol x = x `elem` "+-*/="

The function 'lexIdent' corresponds to the state during lexing where we
have seen the beginning of an identifier (a letter). The remainder of the
identifier is allowed to consist of alphanumeric characters.

> lexIdent :: Char -> String -> [Token]
> lexIdent x ys =
>   case span isAlphaNum ys of
>     (xs, zs) -> Ident (x : xs) : tokenize zs

The function 'lexNumber' corresponds to the state during lexing where we
have seen the beginning of a number. A number is a sequence of digits
followed by an optional fractional part that starts with a period and
is continued by another sequence of digits.

> lexNumber :: Char -> String -> [Token]
> lexNumber x ys =
>   case span isNumber ys of
>     (xs, '.' : zs) -> lexFraction (x : xs) zs
>     (xs,       zs) -> Number (read (x : xs)) : tokenize zs

The 'lexFraction' function takes the string representation of the
integral part and the rest of the input. We expect at least one digit
after a period, otherwise we consider the token to be illegal.

> lexFraction :: String -> String -> [Token]
> lexFraction ns ys =
>   case span isNumber ys of
>     (fs@(_ : _), zs) -> Number (read (ns ++ "." ++ fs)) : tokenize zs
>     ([],         zs) -> Number (read ns) : Err '.' : tokenize zs

This completes the lexer.

We can easily test the lexer by just calling 'tokenize' on a given input
string. We can also define some simple unit tests:

> testsLexer :: Test
> testsLexer =
>   test [
>     "num1" ~: tokenize "1.42"    ~=? [Number 1.42],
>     "num2" ~: tokenize "007"     ~=? [Number 7],
>     "num3" ~: tokenize ".5"      ~=? [Err '.', Number 5],
>     "num4" ~: tokenize "  0.5  " ~=? [Number 0.5],
>     "num5" ~: tokenize "0. 5 "   ~=? [Number 0, Err '.', Number 5],
>     "id1"  ~: tokenize "x13"     ~=? [Ident "x13"],
>     "id2"  ~: tokenize "x1.5"    ~=? [Ident "x1", Err '.', Number 5],
>     "id3"  ~: tokenize "1x"      ~=? [Number 1, Ident "x"],
>     "id4"  ~: tokenize "xyz"     ~=? [Ident "xyz"],
>     "id5"  ~: tokenize "x y z"   ~=? [Ident "x", Ident "y", Ident "z"],
>     "call" ~: tokenize "f(x)"    ~=? [Ident "f", LPar, Ident "x", RPar],
>     "sym1" ~: tokenize "x+y"     ~=? [Ident "x", Symbol '+', Ident "y"],
>     "sym2" ~: tokenize "x++y"    ~=? [Ident "x", Symbol '+', Symbol '+', Ident "y"],
>     "sym3" ~: tokenize "-1"      ~=? [Symbol '-', Number 1]
>   ]

The operator '~:' assigns a name to a test, and the operator '~=?' tests the
two given Haskell expressions for equality. We can run all the above unit
tests by calling

< runTestTT testsLexer

in GHCi.

Abstract syntax
===============

Before we go on, we look at the grammar we want to parse:

  Expression ::= Term { ('+' | '-') Term } | Identifier '=' Expression
  Term       ::= Factor { ('*' | '/') Factor }
  Factor     ::= Number
              |  Identifier
              |  Identifier '(' Expression ')'
              |  '-' Factor
              |  '(' Expression ')'

We turn this into an abstract syntax making the following simplications:

   * we use binary nodes for all the operators,
   * we treat all binary operators except assignment uniformly,
   * we ignore precedence levels because precedence is explicit in the tree,
   * similarly, we drop parentheses,
   * assignment is handled differently because its lhs is restricted to an identifier.

The resulting Haskell datatype is as follows:

> data Tree =
>     BinOp  BinOp Tree Tree -- ^ binary operator
>   | UMinus Tree            -- ^ unary minus
>   | Assign String Tree     -- ^ assignment
>   | Call   String Tree     -- ^ unary function call
>   | Num    Double          -- ^ literal number
>   | Var    String          -- ^ variable reference
>   deriving (Eq, Show)

We make use of the 'BinOp' datatype above, which has constructors for the
four operators we use.

> data BinOp = Plus | Minus | Times | DivBy
>   deriving (Eq, Show)

Parsing
=======

The task of parsing is to transform the tokenized input string into a value of
type 'Tree'. Trying to code parsers directly quickly leads to cluttered code.
Therefore, it makes sense to introduce some helpful abstractions in advance.

Parser combinators
------------------

In the following, we introduce our own extremely simple parser combinator
library.  It is neither very efficient nor particularly user-friendly. But much
more powerful libraries based on the same ideas exist, and they have a very
similar interface.

We start by defining a new datatype for parsers. A parser is a function that
takes as input the sequence of tokens. A parser can fail or produce a result.
If it produces a result, it will consume an initial part of the token list,
but perhaps not the entire input. Therefore, it makes sense to pair the result
with the remaining input. Furthermore, it is helpful to generalize and allow
a parser to have multiple results, to model local ambiguity. These
considerations motivate the following definition for a parser:

> newtype Parser a = P { parse :: [Token] -> [(a, [Token])] }

We could have used 'type' to define a type synonym. But with a few simple basic
parsers, it is actually possible to see 'Parser' as an abstract type, hiding
its internals. We therefore use 'newtype' which defines a new type that is
distinguished from the wrapped type by the type system. The constructor
function 'P' and the selector function 'parse' can be used to convert between
the wrapped and the defined type. Their type signatures are implied by the
'newtype' declaration above:

< P     :: ([Token] -> [(a, [Token])]) -> Parser a
< parse :: Parser a -> ([Token] -> [(a, [Token])])

One of the simplest parser is one that does not look at its input and just
returns a given result. We call this parser 'epsilon':

> epsilon :: a -> Parser a
> epsilon r = P (\ xs -> [(r, xs)])

Another useful extremely basic parser is the one that always fails. We
call it 'zero', and regardless of input it returns the empty list of
results.

> zero :: Parser a
> zero = P (\ xs -> [])

Sooner or later we'll have to consume input. So the next parser function
consumes a single token. Usually, we do not want to consume any arbitrary
token, but rather want to provide a predicate that checks whether the next
token in line is suitable in our current situation. We use a function of
type 'Token -> Maybe a' for this purpose. If the function returns 'Nothing',
we reject the token and fail. If the function returns 'Just x', we treat 'x'
as the payload of the token and return that as the result:

> tok :: (Token -> Maybe a) -> Parser a
> tok p = P (\ xs -> case xs of
>                      (x : xs) | Just r <- p x -> [(r , xs)]
>                      _                        -> [])

We can test this function with the helper functions we defined in the very
beginning.

> testsTok :: Test
> testsTok =
>   test [
>     "tok1" ~: parse (tok toIdent)        (tokenize "xyz") ~=? [("xyz", [])],
>     "tok2" ~: parse (tok toIdent)        (tokenize "1.5") ~=? [],
>     "tok3" ~: parse (tok toNumber)       (tokenize "1.5") ~=? [(1.5, [])],
>     "tok4" ~: parse (tok toLPar)         (tokenize "(")   ~=? [((), [])],
>     "tok5" ~: parse (tok toLPar)         (tokenize "((")  ~=? [((), [LPar])],
>     "tok6" ~: parse (tok toRPar)         (tokenize "((")  ~=? [],
>     "tok7" ~: parse (tok (isSymbol '+')) (tokenize "+-")  ~=? [((), [Symbol '-'])],
>     "tok8" ~: parse (tok (isSymbol '-')) (tokenize "+-")  ~=? []
>   ]

Note that '[]' represents a failed parse. Note that 'tok' expects the correct
token at the beginning of the input. Some of the functions such as 'toLPar'
and 'isSymbol' only check for the correct symbol. There's no payload; in this
case we use the unit type '()' to denote the result. Note that if the input
string contains more than one token, then a successful parse of the first token
pairs the result with the remaining tokens.

We can only do interesting things as soon as we can combine parsers. We
usually want to parse many things in sequence. We therefore introduce a
sequencing combinator. What should its type be? One option that seems
plausible is to collect the result of the first and second parser into a
pair:

< sequ :: Parser a -> Parser b -> Parser (a, b)

However, a sequence of more than two parsers would then result in a parser
producing a nested pair, and it would be awkward to process that pair, as
most functions in Haskell don't work on nested pairs or even tuples at all,
but rather use curried style. With curried style, it turns out to be much
more useful to assume that we can let the first parser in a sequence
return a function, and the second a suitable argument, so that we can let
the combination return the function result:

> sequ :: Parser (a -> b) -> Parser a -> Parser b

This extends nicely to nested sequences:

< \ pf px py -> pf `sequ` px `sequ` py
<   :: Parser (a -> b -> c) -> Parser a -> Parser b -> Parser c

How do we produce parsers returning a function, though? One simple way is
to use 'epsilon'. Here is an example of how to parse two numbers and return
their sum:

> number :: Parser Double
> number = tok toNumber

> twoNumbers :: Parser Double
> twoNumbers = epsilon (+) `sequ` number `sequ` number

We still have to define 'sequ'. We use a list comprehension to achieve that:

> pf `sequ` px = P (\ xs -> [ (f x, zs) | (f, ys) <- parse pf xs,
>                                         (x, zs) <- parse px ys ])

The idea is as follows: we feed the incoming input 'xs' to the first parser
'pf'. That parser yields a number of results (possibly none if it fails).
Each of these results 'f' is paired with a remaining string 'ys'. For each
of these pairs, we want to in turn feed the remaining string 'ys' to the
second parser 'px', and call the resulting pairs of the second parser '(x, zs)'.
The final results are given by applying the results of the first parser to the
results of the second parser, and by using the remaining strings 'zs' after
running both parsers.

We can see that sequencing works as intended by running 'twoNumbers' from above
and 'negNumber':

> negNumber :: Parser Double
> negNumber = epsilon negate `sequ` number

Note that 'negNumber' does consume just one number. The sequencing is used
to change the result.

> testsSequ :: Test
> testsSequ =
>   test [
>     "sequ1" ~: parse twoNumbers [Number 1.5, Number 3.2]       ~=? [(4.7, [])],
>     "sequ2" ~: parse twoNumbers [Number 1.5, LPar]             ~=? [],
>     "sequ3" ~: parse twoNumbers [Number 1, Number 2, Number 4] ~=? [(3, [Number 4])],
>     "sequ4" ~: parse negNumber  [Number 1.5]                   ~=? [(-1.5, [])]
>   ]

One more piece of functionality we need is to handle choice. Often, we want
to parse one of many possible things, and look at the input to decide what
to do. In most cases, we'll expect all but one of the alternatives we provide
to fail. Therefore, implementing choice is very simple: we concatenate all the
results we get from the individual parsers.

> choice :: Parser a -> Parser a -> Parser a
> choice p q = P (\ xs -> parse p xs ++ parse q xs)

Here are a few test cases that also serve as examples:

> testsChoice :: Test
> testsChoice =
>   test [
>     "choice1" ~: parse (twoNumbers `choice` negNumber) [Number 1.5]         ~=? [(-1.5, [])],
>     "choice2" ~: parse (twoNumbers `choice` negNumber) [Number 1, Number 2] ~=? [(3, []), (-1, [Number 2])]
>   ]

The second test above is an exampe of a locally ambiguous parser. We can either
consume both numbers and return their sum, or we can consume just the first and
negate it. Of course, the wider context may disambiguate this choice again.

We're nearly done. The final parser we're going to introduce is the one that
matches the end of the input. It won't consume anything further, but only succeed
if we actually have reached the end:

> eof :: Parser ()
> eof = P (\ xs -> if L.null xs then [((), [])] else [])

A common interface
------------------

Actually, it turns out that not only parsers support the operations we have
introduced above, such as 'epsilon', 'zero', 'sequ' and 'choice'. Other types
support very similar operations. Therefore, Haskell provides a type class for
these, and we can use nice symbolic names for these operations. Furthermore,
we win quite a few derived functions that are provided by the library in terms
of these basic functions:

> instance Applicative Parser where
>   pure  = epsilon
>   (<*>) = sequ

So, we can use 'pure' for 'epsilon', and more importantly, '<*>' for 'sequ'.

> instance Alternative Parser where
>   empty = zero
>   (<|>) = choice

The new name for 'zero' is 'empty', and we can use '<|>' for 'choice'.

It is furthermore worth noting that the combination

< epsilon f `sequ` ...

to change the type of a parser is really frequent. If we abstract it as a
function, we obtain:

> adapt :: (a -> b) -> Parser a -> Parser b
> adapt f p = epsilon f `sequ` p

This is also a type class function in Haskell, called 'fmap':

> instance Functor Parser where
>   fmap = adapt

There's also a symbolic synonym for 'fmap' called '<$>'.

Using the new names, we can write 'twoNumbers' from above as follows:

> twoNumbers' :: Parser Double
> twoNumbers' = (+) <$> number <*> number

It is worth noting that none of the parser-specific functions we have
implemented so far (except for the examples) are specific to our grammar or
even token type. All we did is that we assumed a 'Token' datatype to exist.
We then defined very general functions that make sense for parsers. It is
therefore no surprise that we could have used predefined library parsers
instead of defining our own. We chose to define our own because it is
relatively easy to do so and illustrates how to design libraries like this
in Haskell.

Handling left-associative operators
-----------------------------------

It is time to look at our grammar again. The first line reads:

  Expression ::= Term { ('+' | '-') Term } | Identifier '=' Expression

An easier way of writing this would have been:

  Expression ::= Expression ('+' | '-') Term | Identifier '=' Expression

However, if we translate this line naively into a parser for expressions
as follows,

< expression = convertResult <$> expression <*> plusMinus <*> term <|> ...

(omitting definitions of 'convertResult' and 'plusMinus' here), it turns
out that 'expression' calls 'expression' before consuming any input, and
in our simple parser combinator library this results in an infinite loop.
We should therefore try to translate the left-recursion-free form given
above more directly.

For this, we need to first consider how to parse a sequence of zero or
more occurrences of something. This is a derived parser called 'many' that
we have available for free now, because we're using the 'Applicative' and
'Alternative' classes. However, we could have easily defined it ourselves:

< many :: Parser a -> Parser [a]
< many p = (:) <$> p <*> many p <|> pure []

Note that '<|>' binds weaker than '<$>' and '<*>'. So in order to parse
many 'p's, we try to parse a single 'p' followed by many 'p's, combining
their results using '(:)'; or we consume nothing and return an empty list.

> testsMany :: Test
> testsMany =
>   test [
>     "many1" ~: parse (many number) (tokenize "1 2 3") ~=?
>        [([1, 2, 3], []),
>         ([1, 2],    [Number 3.0]),
>         ([1],       [Number 2.0,Number 3.0]),
>         ([],        [Number 1.0,Number 2.0,Number 3.0])],
>     "many2" ~: parse (const <$> many number <*> eof) (tokenize "1 2 3") ~=?
>        [([1, 2, 3], [])]
>   ]

We see that 'many' is in general highly ambiguous, as it can consume any number
of occurrences of the specified component. However, the second test demonstrates
how the context can help disamguating. If we force that the sequence of numbers
is followed by the end of input, we have only one possible result left.

Now we are going to build a combinator based on 'many' that is specifically
tailored to handle rules such as

  Term { ('+' | '-') Term }

where we have a chain of terms separated by a binary operator. We call this
combinator 'chainl1'. The '1' because we don't accept an empty sequence here,
and the 'l' because we're going to treat the operator as left-associative.

Let's jump right to the definition, and explain it afterwards:

> chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
> chainl1 px pop = L.foldl (flip ($)) <$> px <*> (many (flip <$> pop <*> px))

Assume we have an input to parse that looks as follows:

  1 + 2 + 3 + 4 + 5

Then 'chainl1' will take a parser to parse the terms, i.e., the numbers in
this case. And it will take a parser to parse the operators. Now, the operator
parser should actually return a binary operator on the term type, so it could
return actual addition if the term parser were to return numbers in this case.

Now 'chainl1' parses the first term (the '1') followed by many pairs of an
operator and another term each. So it'll roughly see the input as follows:

  1 | + 2 | + 3 | + 4 | + 5

We use 'flip' in the argument to 'many' so that the binary infix operator is
already applied to it's right argument, rather than its first left argument.
This corresponds to the situation we now have. The partially applied operators
are then returned in a list by 'many'.

  1 | [(+ 2), (+ 3), (+ 4), (+ 5)]

Finally, we use 'foldl' to traverse the resulting list from left to right,
starting with the term in the beginning as our accumulator, and apply the
results from the list. This will lead to the desired left-associative
interpretation as

  (((1 + 2) + 3) + 4) + 5

Once again, there's nothing about 'chainl1' that is specific to our grammar.
This combinator as well as its counterpart 'chainr1' are generally useful for
parsing expression grammars and are therefore provided by most parser
combinator libraries in Haskell.

Transcribing the grammar
------------------------

After having done all the basic work, it is now straight-forward to define a
parser for our grammar:

  Expression ::= Term { ('+' | '-') Term } | Identifier '=' Expression
  Term       ::= Factor { ('*' | '/') Factor }
  Factor     ::= Number
              |  Identifier
              |  Identifier '(' Expression ')'
              |  '-' Factor
              |  '(' Expression ')'

Let us define a few simple wrappers around 'tok', similar to 'number' that
we have already defined above:

> ident :: Parser String
> ident = tok toIdent
>
> symbol :: Char -> Parser ()
> symbol s = tok (isSymbol s)
>
> lpar, rpar :: Parser ()
> lpar = tok toLPar
> rpar = tok toRPar

Now we can define one function per nonterminal:

> expression :: Parser Tree
> expression =   chainl1 term (BinOp Plus <$ symbol '+' <|> BinOp Minus <$ symbol '-')
>            <|> Assign <$> tok toIdent <* symbol '=' <*> expression

We haven't seen '<$' and '<*' before. They are variants of '<$>' and '<*>' that
ignore the result of the argument directly to their right. We could have defined
the second line as

<        ... <|> (\ x _ e -> Assign x e) <$> tok toIdent <*> symbol '=' <*> expression

without using this new function. It would just have meant that we have to pick
up the unneeded result of 'symbol' and explicitly drop it in the function we
use to convert the results.

> term :: Parser Tree
> term = chainl1 factor (BinOp Times <$ symbol '*' <|> BinOp DivBy <$ symbol '/')

> factor :: Parser Tree
> factor =   Num    <$> tok toNumber
>        <|> Var    <$> tok toIdent
>        <|> Call   <$> tok toIdent  <* tok toLPar <*> expression <* tok toRPar
>        <|> UMinus <$  symbol '-' <*> factor
>        <|>            tok toLPar *> expression <* tok toRPar

This completes the parser. Note how close it is to the EBNF version.

Running the lexer and parser
----------------------------

The function 'toTree' takes a string, tokenizes it, tries to parse the complete
string as an expression (using 'eof' to enforce the complete string to be
parsed). We then check if there is at least one result and return it, otherwise
fail.

Note that the simple parser combinators we defined above give no hint about the
position and nature of an error if one occurs. Proper parser combinator
libraries provided for Haskell of course do that.

> toTree :: String -> Maybe Tree
> toTree xs =
>   case parse (expression <* eof) (tokenize xs) of
>     (r , _) : _ -> Just r
>     _           -> Nothing

Let's test a few things:

> testsToTree :: Test
> testsToTree =
>   test [
>     "leftplus" ~: toTree "1 + 2 + 3" ~=?
>        Just (BinOp Plus (BinOp Plus (Num 1) (Num 2)) (Num 3)),
>     "prio"     ~: toTree "1 + 2 * 3" ~=?
>        Just (BinOp Plus (Num 1) (BinOp Times (Num 2) (Num 3)))
>   ]

Interpreting the tree
=====================

We now want to write an interpreter for the tree.

We use two separate symbol tables, for functions and for variables.  Currently,
only variables can be defined at run-time, whereas functions are static.

> type Functions = Map String (Double -> Double)
> type Vars      = Map String Double

Initial functions and variables
-------------------------------

We provide some predefined functions and variables that can be used:

> functions :: Functions
> functions =
>   M.fromList [
>     ("sin" , sin ),
>     ("cos" , cos ),
>     ("tan" , tan ),
>     ("asin", asin),
>     ("acos", acos),
>     ("atan", atan),
>     ("sqr" , \ x -> x * x),
>     ("sqrt", sqrt),
>     ("exp" , exp),
>     ("log" , log)
>   ]

> vars :: Vars
> vars =
>   M.fromList [
>     ("pi", pi),
>     ("e",  exp 1)
>   ]

The following function is the entire interpreter. We take the function
table and the tree. The ultimate result should be a 'Double', but we
maintain a state of type 'Vars' in this computation. Finally, we want
to maintain this state even through an interactive read-eval-print loop,
that's why we allow another effect type 'm' to be spliced in.

TODO: The above needs more explanation. Actually, probably we could define
'run' using explicit state passing or a continuation first, and then appeal
to monads and monad transformers.

Anyway, this is the one based on the state monad:

> run :: (Functor m, Monad m) => Functions -> Tree -> StateT Vars m Double
> run funs = go
>   where
>     go (UMinus t)       = negate <$> go t
>     go (Num n)          = return n
>     go (Var x)          = findWithDefault 0 x <$> get
>     go (Assign x t)     = go t >>= \ r -> modify (M.insert x r) >> return r
>     go (BinOp op t1 t2) = liftM2 (runOp op) (go t1) (go t2)
>     go (Call f t)       = findWithDefault (const 0) f funs <$> go t

None of the cases is particularly tricky. In the 'Var' and 'Call'
cases, we perform lookups in the appropriate symbol tables, and
assume '0' and 'const 0' if the variable or function is not found,
respectively. In the 'Assign' case, we actually update the symbol
table with the result computed for the right hand side. The assignment
as a whole has the value of its right hand side.

For comparison, this is the run function based on continuations:

> run' :: Functions -> Tree -> Vars -> (Vars -> Double -> r) -> r
> run' funs = go
>   where
>     go (UMinus t)       s k = go t s (\ s' r -> k s' (negate r))
>     go (Num n)          s k = k s n
>     go (Var x)          s k = k s (findWithDefault 0 x s)
>     go (Assign x t)     s k = go t s (\ s' r -> k (M.insert x r s') r)
>     go (BinOp op t1 t2) s k = go t1 s (\ s' r1 -> go t2 s (\ s'' r2 -> k s'' (runOp op r1 r2)))
>     go (Call f t)       s k = go t s (\ s' r -> k s' (findWithDefault (const 0) f funs r))

Both run functions need the following function to map operators to Haskell
functions:

> runOp :: BinOp -> Double -> Double -> Double
> runOp Plus  = (+)
> runOp Minus = (-)
> runOp Times = (*)
> runOp DivBy = (/)

Interactive loop
================

Here is a simple wrapper around run that reads lines from the user, parses them
and evaluates them, maintaining the current symbol table for variables
throughout the interaction. An empty line quits the interaction. Input with
parse or lex errors (lex errors will result in parse errors subsequently) is
ignored and a new line is prompted for.

> runInteractive :: IO ()
> runInteractive = runStateT loop vars >> return ()
>   where
>     loop :: StateT Vars IO ()
>     loop = do
>       r <- liftIO getLine
>       unless (L.null r) $ do
>         case toTree r of
>           Nothing -> liftIO (putStrLn "invalid input")
>           Just t  -> run functions t >>= liftIO . putStrLn . ("  "++) . show
>         loop

And similarly for the continuation version of 'run':

> runInteractive' :: IO ()
> runInteractive' = loop vars
>   where
>     loop :: Vars -> IO ()
>     loop s = do
>       r <- getLine
>       unless (L.null r) $ do
>         case toTree r of
>           Nothing -> putStrLn "invalid input" >> loop s
>           Just t  -> run' functions t s $ \ s' r -> do
>                        putStrLn ("  " ++ show r)
>                        loop s'

Main program
============

We just start the interactive loop.

> main :: IO ()
> main = runInteractive'

Batch interpreter
=================

A nice feature of our interpreter (both versions) is that it's very
simple to run it non-interactively, without any IO at all. Here, we
take a list of input lines, ignore all invalid input and return the
result of all the expressions:

> runBatch :: [String] -> [Double]
> runBatch xs =
>   fst (runState (mapM (run functions) (catMaybes (L.map toTree xs))) vars)

This is of course great for testing:

> testsRun :: Test
> testsRun =
>   test [
>     "run1" ~: runBatch ["x = 2", "y = 3", "x = x + y"] ~=? [2, 3, 5],
>     "run2" ~: runBatch ["x = y = log(e)", "x", "y"]    ~=? [1, 1, 1]
>   ]

All tests
=========

For easy testing:

> allTests :: Test
> allTests =
>   test [
>     testsLexer, testsTok, testsSequ, testsChoice, testsMany, testsToTree, testsRun
>   ]

Tests can be run in GHCi using

< runTestTT allTests
