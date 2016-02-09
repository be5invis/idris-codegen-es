module Js.BrowserNetwork

import Js.IO
import Js.BrowserForeigns

httpGet : String -> ASync String
httpGet url = MkASync $ httpGet_raw url

httpPost : String -> String -> ASync String
httpPost url body = MkASync $ httpPost_raw url body
