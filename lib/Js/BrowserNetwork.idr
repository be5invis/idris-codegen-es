module Js.BrowserNetwork

import Js.BrowserForeigns
import public Js.ServiceTypes

export
httpGet : String -> ASync String
httpGet url = MkASync $ httpGet_raw url

export
httpPost : String -> String -> ASync String
httpPost url body = MkASync $ httpPost_raw url body

export
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

export
CallServTy : List Service -> String -> Type
CallServTy xs y = ServiceTy $ getServ y xs

export
callServ : (ls: List Service) -> (name:String) -> CallServTy ls name
callServ ls name = runServ $ getServ name ls
