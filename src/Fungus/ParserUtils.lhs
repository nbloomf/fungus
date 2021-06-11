> module Fungus.ParserUtils where

> import qualified Data.Text as T
> import           Test.QuickCheck
> import           Text.Parsec
> import           Text.Parsec.Text



> data SourceLoc
>   = Q                                      -- "nowhere"
>   | SourceLoc T.Text (Int, Int) (Int, Int) -- line:col range
>   deriving (Eq, Ord, Show)
> 
> instance Arbitrary SourceLoc where
>   arbitrary = return Q

> getFileName :: Parser T.Text
> getFileName = T.pack <$> sourceName <$> getPosition
> 
> getLineCol :: Parser (Int, Int)
> getLineCol = do
>   pos <- getPosition
>   return (sourceLine pos, sourceColumn pos)
