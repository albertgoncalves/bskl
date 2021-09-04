import qualified GMachine as G
import qualified Parser as P
import qualified Template as T

main :: IO ()
main = do
  P.tests
  T.tests
  G.tests
