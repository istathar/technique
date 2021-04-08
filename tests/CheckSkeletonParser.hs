{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CheckSkeletonParser (
    checkSkeletonParser,
    main,
) where

import Core.System
import Core.Text
import Technique.Language
import Technique.Parser
import Technique.Quantity
import Test.Hspec
import Text.Megaparsec hiding (Label)

main :: IO ()
main = do
    finally (hspec checkSkeletonParser) (putStrLn ".")

checkSkeletonParser :: Spec
checkSkeletonParser = do
    describe "Parse procfile header" $ do
        it "correctly parses a complete magic line" $ do
            parseMaybe pMagicLine "% technique v2\n" `shouldBe` Just 2
        it "errors if magic line has incorrect syntax" $ do
            parseMaybe pMagicLine "%\n" `shouldBe` Nothing
            parseMaybe pMagicLine "%technique\n" `shouldBe` Nothing
            parseMaybe pMagicLine "% technique\n" `shouldBe` Nothing
            parseMaybe pMagicLine "% technique \n" `shouldBe` Nothing
            parseMaybe pMagicLine "% technique v\n" `shouldBe` Nothing
            parseMaybe pMagicLine "% technique  v2\n" `shouldBe` Nothing
            parseMaybe pMagicLine "% technique v2 asdf\n" `shouldBe` Nothing

        it "correctly parses an SPDX header line" $ do
            parseMaybe pSpdxLine "! BSD-3-Clause\n" `shouldBe` Just ("BSD-3-Clause", Nothing)
        it "correctly parses an SPDX header line with Copyright" $ do
            parseMaybe pSpdxLine "! BSD-3-Clause; (c) 2019 Kermit le Frog\n" `shouldBe` Just ("BSD-3-Clause", Just "2019 Kermit le Frog")
        it "errors if SPDX line has incorrect syntax" $ do
            parseMaybe pSpdxLine "!\n" `shouldBe` Nothing
            parseMaybe pSpdxLine "! Public-Domain;\n" `shouldBe` Nothing
            parseMaybe pSpdxLine "! Public-Domain; (\n" `shouldBe` Nothing
            parseMaybe pSpdxLine "! Public-Domain; (c)\n" `shouldBe` Nothing
            parseMaybe pSpdxLine "! Public-Domain; (c) \n" `shouldBe` Nothing

        it "correctly parses a complete technique program header" $ do
            parseMaybe
                pTechnique
                [quote|
% technique v0
! BSD-3-Clause
            |]
                `shouldBe` Just
                    ( Technique
                        { techniqueVersion = 0
                        , techniqueLicense = "BSD-3-Clause"
                        , techniqueCopyright = Nothing
                        , techniqueBody = []
                        }
                    )

    describe "Parses a proecdure declaration" $ do
        it "name parser handles valid identifiers" $ do
            parseMaybe pIdentifier "" `shouldBe` Nothing
            parseMaybe pIdentifier "i" `shouldBe` Just (Identifier "i")
            parseMaybe pIdentifier "ingredients" `shouldBe` Just (Identifier "ingredients")
            parseMaybe pIdentifier "roast_turkey" `shouldBe` Just (Identifier "roast_turkey")
            parseMaybe pIdentifier "1x" `shouldBe` Nothing
            parseMaybe pIdentifier "x1" `shouldBe` Just (Identifier "x1")

        it "type parser handles valid type names" $ do
            parseMaybe pType "" `shouldBe` Nothing
            parseMaybe pType "I" `shouldBe` Just (Type "I")
            parseMaybe pType "Ingredients" `shouldBe` Just (Type "Ingredients")
            parseMaybe pType "RoastTurkey" `shouldBe` Just (Type "RoastTurkey")
            parseMaybe pType "Roast_Turkey" `shouldBe` Nothing
            parseMaybe pType "2Dinner" `shouldBe` Nothing
            parseMaybe pType "Dinner3" `shouldBe` Just (Type "Dinner3")

        it "handles a name, parameters, and a type signature" $ do
            parseMaybe pProcedureDeclaration "roast_turkey i : Ingredients -> Turkey"
                `shouldBe` Just (Identifier "roast_turkey", [Identifier "i"], [Type "Ingredients"], [Type "Turkey"])
            parseMaybe pProcedureDeclaration "roast_turkey  i  :  Ingredients  ->  Turkey"
                `shouldBe` Just (Identifier "roast_turkey", [Identifier "i"], [Type "Ingredients"], [Type "Turkey"])
            parseMaybe pProcedureDeclaration "roast_turkey:Ingredients->Turkey"
                `shouldBe` Just (Identifier "roast_turkey", [], [Type "Ingredients"], [Type "Turkey"])

    describe "Literals" $ do
        it "quoted string is interpreted as text" $ do
            parseMaybe stringLiteral "\"Hello world\"" `shouldBe` Just "Hello world"
            parseMaybe stringLiteral "\"Hello \\\"world\"" `shouldBe` Just "Hello \"world"
            parseMaybe stringLiteral "\"\"" `shouldBe` Just ""

        it "positive integers" $ do
            parseMaybe numberLiteral "42" `shouldBe` Just 42
            parseMaybe numberLiteral "0" `shouldBe` Just 0
            parseMaybe numberLiteral "1a" `shouldBe` Nothing

    describe "Parses quantities" $ do
        it "a number is a Number" $ do
            parseMaybe pQuantity "42" `shouldBe` Just (Number 42)
            parseMaybe pQuantity "-42" `shouldBe` Just (Number (-42))

        it "a quantity with units is a Quantity" $ do
            parseMaybe pQuantity "149 kg" `shouldBe` Just (Quantity (Decimal 149 0) (Decimal 0 0) 0 "kg")

        it "a quantity with mantissa, magnitude, and units is a Quantity" $ do
            parseMaybe pQuantity "5.9722 × 10^24 kg" `shouldBe` Just (Quantity (Decimal 59722 4) (Decimal 0 0) 24 "kg")

        it "a quantity with mantissa, uncertainty, and units is a Quantity" $ do
            parseMaybe pQuantity "5.9722 ± 0.0006 kg" `shouldBe` Just (Quantity (Decimal 59722 4) (Decimal 6 4) 0 "kg")

        it "a quantity with mantissa, uncertainty, magnitude, and units is a Quantity" $ do
            parseMaybe pQuantity "5.9722 ± 0.0006 × 10^24 kg" `shouldBe` Just (Quantity (Decimal 59722 4) (Decimal 6 4) 24 "kg")

        it "same quantity, with superscripts, is a Quantity" $ do
            parseMaybe pQuantity "5.9722 ± 0.0006 × 10²⁴ kg" `shouldBe` Just (Quantity (Decimal 59722 4) (Decimal 6 4) 24 "kg")

        it "negative Quantities also parse" $ do
            parseMaybe pQuantity "1234567890" `shouldBe` Just (Number 1234567890)
            parseMaybe pQuantity "-1234567890" `shouldBe` Just (Number (-1234567890))
            parseMaybe pQuantity "3.14 ± 0.01 m" `shouldBe` Just (Quantity (Decimal 314 2) (Decimal 001 2) 0 "m")
            parseMaybe pQuantity "-3.14 ± 0.01 m" `shouldBe` Just (Quantity (Decimal (-314) 2) (Decimal 001 2) 0 "m")

    describe "Parses attributes" $ do
        it "recognizes a role marker" $ do
            parseMaybe pAttribute "@butler" `shouldBe` Just (Role (Identifier "butler"))
        it "recognizes a place marker" $ do
            parseMaybe pAttribute "#library" `shouldBe` Just (Place (Identifier "library"))
        it "recognizes any" $ do
            parseMaybe pAttribute "@*" `shouldBe` Just (Role (Identifier "*"))
            parseMaybe pAttribute "#*" `shouldBe` Just (Place (Identifier "*"))

    describe "Parses expressions" $ do
        it "an empty input an error" $ do
            parseMaybe pExpression "" `shouldBe` Nothing

        it "an pair of parentheses is None" $ do
            parseMaybe pExpression "()" `shouldBe` Just (None 0)

        it "a quoted string is a Text" $ do
            parseMaybe pExpression "\"Hello world\"" `shouldBe` Just (Text 0 "Hello world")
            parseMaybe pExpression "\"\"" `shouldBe` Just (Text 0 "")

        it "a bare identifier is a Variable" $ do
            parseMaybe pExpression "x" `shouldBe` Just (Variable 0 [Identifier "x"])

        it "an identifier, space, and then expression is an Application" $ do
            parseMaybe pExpression "a x"
                `shouldBe` Just (Application 0 (Identifier "a") (Variable 2 [Identifier "x"]))

        it "a quoted string is a Literal Text" $ do
            parseMaybe pExpression "\"Hello world\"" `shouldBe` Just (Text 0 "Hello world")

        it "a bare number is a Literal Number" $ do
            parseMaybe pExpression "42" `shouldBe` Just (Amount 0 (Number 42))

        it "a nested expression is parsed as Grouped" $ do
            parseMaybe pExpression "(42)" `shouldBe` Just (Grouping 0 (Amount 1 (Number 42)))

        it "an operator between two expressions is an Operation" $ do
            parseMaybe pExpression "x & y"
                `shouldBe` Just
                    ( Operation
                        0
                        WaitBoth
                        (Variable 0 [Identifier "x"])
                        (Variable 4 [Identifier "y"])
                    )

        it "handles tablet with one binding" $ do
            parseMaybe pExpression "[ \"King\" ~ george ]"
                `shouldBe` Just
                    ( Object
                        0
                        ( Tablet
                            [ Binding (Label "King") (Variable 11 [Identifier "george"])
                            ]
                        )
                    )

        it "handles tablet with multiple bindings" $ do
            parseMaybe pExpression "[ \"first\" ~ \"George\" \n \"last\" ~ \"Windsor\" ]"
                `shouldBe` Just
                    ( Object
                        0
                        ( Tablet
                            [ Binding (Label "first") (Text 12 "George")
                            , Binding (Label "last") (Text 32 "Windsor")
                            ]
                        )
                    )
    {-
      it "handles tablet with alternate single-line syntax" $
        let expected =
              Just
                ( Object
                    ( Tablet
                        [ Binding "name" (Variable [Identifier "n"]),
                          Binding "king" (Amount (Number 42))
                        ]
                    )
                )
         in do
              parseMaybe pExpression "[\"name\" ~ n,\"king\" ~ 42]" `shouldBe` expected
              parseMaybe pExpression "[\"name\" ~ n , \"king\" ~ 42]" `shouldBe` expected
    -}

    describe "Parses statements containing expressions" $ do
        it "a blank line is a Blank" $ do
            parseMaybe pStatement "\n" `shouldBe` Just (Blank 0)

        it "considers a single identifier an Execute" $ do
            parseMaybe pStatement "x"
                `shouldBe` Just (Execute 0 (Variable 0 [Identifier "x"]))

        it "considers a line with an '=' to be an Assignment" $ do
            parseMaybe pStatement "answer = 42"
                `shouldBe` Just (Assignment 0 [Identifier "answer"] (Amount 9 (Number 42)))

    describe "Parses blocks of statements" $ do
        it "an empty block is a [] (special case)" $ do
            parseMaybe pBlock "{}" `shouldBe` Just (Block [])

        it "a block with a newline (only) is []" $ do
            parseMaybe pBlock "{\n}" `shouldBe` Just (Block [])

        it "a block with single statement surrounded by a newlines" $ do
            parseMaybe pBlock "{\nx\n}"
                `shouldBe` Just
                    ( Block
                        [ Execute 2 (Variable 2 [Identifier "x"])
                        ]
                    )
            parseMaybe pBlock "{\nanswer = 42\n}"
                `shouldBe` Just
                    ( Block
                        [ (Assignment 2 [Identifier "answer"] (Amount 11 (Number 42)))
                        ]
                    )

        it "a block with a blank line contains a Blank" $ do
            parseMaybe pBlock "{\nx1\n\nx2\n}"
                `shouldBe` Just
                    ( Block
                        [ Execute 2 (Variable 2 [Identifier "x1"])
                        , Blank 5
                        , Execute 6 (Variable 6 [Identifier "x2"])
                        ]
                    )

        it "a block with multiple statements separated by newlines" $ do
            parseMaybe pBlock "{\nx\nanswer = 42\n}"
                `shouldBe` Just
                    ( Block
                        [ Execute 2 (Variable 2 [Identifier "x"])
                        , Assignment 4 [Identifier "answer"] (Amount 13 (Number 42))
                        ]
                    )

        it "a block with multiple statements separated by semicolons" $ do
            parseMaybe pBlock "{x ; answer = 42}"
                `shouldBe` Just
                    ( Block
                        [ Execute 1 (Variable 1 [Identifier "x"])
                        , Series 3
                        , Assignment 5 [Identifier "answer"] (Amount 14 (Number 42))
                        ]
                    )

        it "consumes whitespace in inconvenient places" $ do
            parseMaybe pBlock "{ \n }"
                `shouldBe` Just (Block [])
            parseMaybe pBlock "{ \n x \n }"
                `shouldBe` Just
                    ( Block
                        [ Execute 4 (Variable 4 [Identifier "x"])
                        ]
                    )
            parseMaybe pBlock "{ \n (42)    \n}"
                `shouldBe` Just
                    ( Block
                        [ Execute 4 (Grouping 4 (Amount 5 (Number 42)))
                        ]
                    )
            parseMaybe pBlock "{ \n (42 )    \n}"
                `shouldBe` Just
                    ( Block
                        [ Execute 4 (Grouping 4 (Amount 5 (Number 42)))
                        ]
                    )
            parseMaybe pBlock "{ answer = 42 ; }"
                `shouldBe` Just
                    ( Block
                        [ Assignment 2 [Identifier "answer"] (Amount 11 (Number 42))
                        , Series 14
                        ]
                    )

    describe "Parses a procedure declaration" $ do
        it "simple declaration " $ do
            parseMaybe pProcedureDeclaration "f x : X -> Y"
                `shouldBe` Just (Identifier "f", [Identifier "x"], [Type "X"], [Type "Y"])

        it "declaration with multiple variables and input types" $ do
            parseMaybe pProcedureDeclaration "after_dinner i,s,w : IceCream,Strawberries,Waffles -> Dessert"
                `shouldBe` Just
                    ( Identifier "after_dinner"
                    , [Identifier "i", Identifier "s", Identifier "w"]
                    , [Type "IceCream", Type "Strawberries", Type "Waffles"]
                    , [Type "Dessert"]
                    )

        it "handles spurious whitespace" $ do
            parseMaybe pProcedureDeclaration "after_dinner   i ,s ,w  :  IceCream ,Strawberries,  Waffles -> Dessert"
                `shouldBe` Just
                    ( Identifier "after_dinner"
                    , [Identifier "i", Identifier "s", Identifier "w"]
                    , [Type "IceCream", Type "Strawberries", Type "Waffles"]
                    , [Type "Dessert"]
                    )

    describe "Parses a the code for a complete procedure" $ do
        it "parses a declaration and block" $ do
            parseMaybe pProcedureCode "f : X -> Y\n{ x }\n"
                `shouldBe` Just
                    ( emptyProcedure
                        { procedureOffset = 0
                        , procedureName = Identifier "f"
                        , procedureInput = [Type "X"]
                        , procedureOutput = [Type "Y"]
                        , procedureBlock = Block [Execute 13 (Variable 13 [Identifier "x"])]
                        }
                    )
