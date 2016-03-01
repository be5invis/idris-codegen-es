module Js.BrowserNetwork

import Js.IO
import Js.BrowserForeigns
import public Js.ServiceTypes

public
httpGet : String -> ASync String
httpGet url = MkASync $ httpGet_raw url

public
httpPost : String -> String -> ASync String
httpPost url body = MkASync $ httpPost_raw url body

public
ServiceTy : Maybe Service -> Type
ServiceTy Nothing = (Void -> ASync (Either String Void))
ServiceTy (Just (MkService _ a b _)) = (a -> ASync b)

runServ : (ms:Maybe Service) -> ServiceTy ms
runServ Nothing = void
runServ (Just (MkService s _ _ (_, enc, dec, _)))=
  \x => decaux <$> httpPost s (enc x)
  where
    decaux x =
      case dec x of
        Right z => z

public
CallServTy : List Service -> String -> Type
CallServTy xs y = ServiceTy $ getServ y xs

public
callServ : (ls: List Service) -> (name:String) -> CallServTy ls name
callServ ls name = runServ $ getServ name ls
