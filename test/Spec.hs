{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
import           Data.Aeson       (Value, defaultOptions)
import           Data.Aeson.Flow
import           Data.Proxy       (Proxy (..))
import           Data.Text        (Text)
import           Data.Vector      (Vector)
import           GHC.Generics
import           Test.Tasty
import           Test.Tasty.HUnit

data User = User
  { username  :: Text
  , realname  :: Maybe Text
  , dob       :: Maybe (Int, Int, Int)
  , extraInfo :: Value
  } deriving (Generic)

instance FlowTyped User

data Recur = Recur
  { asdf   :: Int
  , stuff  :: [User]
  , recurs :: [Recur]
  } deriving (Generic)

instance FlowTyped Recur

data Adt = Yeah | Nah | Couldbe Int
  deriving (Generic)

instance FlowTyped Adt

ft :: FlowTyped a => Proxy a -> FlowType
ft = flowType defaultOptions

main :: IO ()
main = defaultMain $ testGroup "aeson-flowtyped"
  [ testCase "nullable" $
     showFlowType (ft (Proxy :: Proxy (Maybe Int))) @=?
     showFlowType (Fix (Nullable (Fix (Prim Number))))

  , testCase "array" $ do
     showFlowType (ft (Proxy :: Proxy [Int])) @=?
       showFlowType (Fix (Array (Fix (Prim Number))))

     showFlowType (ft (Proxy :: Proxy (Vector Int))) @=?
       showFlowType (Fix (Array (Fix (Prim Number))))

    -- XXX: actually use Eq

  , testCase "User export" $
    assertEqual
    "User export type"
    "export type User = {|\n\
    \  extraInfo: mixed,\n\
    \  tag: 'User',\n\
    \  realname: ?string,\n\
    \  username: string,\n\
    \  dob: ?[number,number,number] |}"
    (exportFlowTypeAs defaultOptions
     Nothing
     (Proxy :: Proxy User))

  , testCase "Recursive type export" $
    assertEqual
    "Recursive type"
    "export type Recur = {|\n\
    \  tag: 'Recur',\n\
    \  stuff: User[],\n\
    \  recurs: Recur[],\n\
    \  asdf: number |}"
    (exportFlowTypeAs defaultOptions
     Nothing
     (Proxy :: Proxy Recur))


  ]
