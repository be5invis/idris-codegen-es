module Js.BrowserUtils

import Js.BrowserBase

export
button : a -> String -> View a
button val lbl =
  leafView
    "button"
    SUnit
    ()
    draw
    (\_ => pure ())
    updEv
  where
    draw =
      do
        appendNode "button" root
        pure ()
    updEv _ _ = pure ((), Just val)

export
text : String -> View a
text s =
  leafView
    "text"
    SString
    ""
    (pure ())
    upd
    (\_,x => pure (x, Nothing))
  where
    upd x =
      if x == s then pure x
        else
          do
            setText s root
            pure s

export
textinput' : Maybe String -> View String
textinput' s =
  leafView
    "textinput"
    SUnit
    ()
    draw
    upd
    (\e, _ => pure ((), Just e))
  where
    draw = do
      mi <- appendNode "input" root
      case mi of
        Just i => registEvent i "change" targetValue
    upd _ =
      case s of
        Nothing => pure ()

export
textinput : View String
textinput = textinput' Nothing
