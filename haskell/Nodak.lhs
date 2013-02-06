
> module Nodak where

> data Node = Node NId Value TimeStamp
> type NId = Integer
> type Name = String
> type Value = String
> type TimeStamp = String -- @TODO: int?

> data Arc = Arc AId NId NId NId
> type AId = Integer
> type Match = Maybe Node

> type KB = IO -- @TODO

> type Object = ([Arc],[Arc])


Arc - Centric API
-----------------

> declare :: Node -> Node -> Node -> AId -> KB ()
> declare sub rel obj = undefined

> fetch :: AId -> Arc
> fetch arcId = undefined

> match :: Match -> Match -> Match -> [Node]
> match = undefined

> retract :: AId -> KB ()
> retract = undefined

> update :: AId -> Node -> Node -> Node -> KB ()
> update = undefined


Node - Centric API
------------------

> storeNode :: Name -> Value -> KB ()
> storeNode = undefined

> getIncoming :: Name -> [Arc] -> KB ()
> getIncoming = undefined

> getOutgoing :: Name -> [Arc] -> KB ()
> getOutgoing = undefined


> rename :: Name -> Name -> KB ()
> rename old new = undefined

> assemble :: Name -> Object -> KB ()
> assemble = undefined


