module Data.Aeson.Flow where
import           Data.Aeson
import           Data.HashMap.Strict (HashMap)
import           Data.Map.Strict     (Map)
import           Data.Text           (Text)
import           Data.Vector         (Vector)

data FlowType
  = ObjectType !(Map Text FlowType)
  | MapType !(Map Text FlowType)
  | ArrayType !FlowType
  | TupleType !(Vector FlowType)
  | PolyAppType !Text !(Vector FlowType)
  | BooleanType
  | NumberType
  | AnyType
  | StringType
  | VoidType
  | MixedType
  | NullableType !FlowType
  | LiteralType !Value
  deriving (Show, Read, Eq, Ord)

flowTypeValue :: Value -> FlowType
flowTypeValue = undefined

d :: Int
d = ()

