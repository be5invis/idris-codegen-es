module Js.BrowserUtils

import Js.BrowserBase

export
button : a -> String -> View a
button val lbl =
  mkView
    "button"
    False
    ()
    draw
    upd
    []
  where
    draw =
      do
        appendNode "button" root
        pure []
    upd _ _ = pure ((), Just val)

export
text : String -> View a
text s =
  mkView
    "text"
    False
    ()
    draw
    (\_,_ => pure ((), Nothing))
    []
  where
    draw =
      do
        setText s root
        pure []

export
textinput' : Maybe String -> View String
textinput' s =
  mkView
    "textinput"
    False
    (lowerMaybe s)
    draw
    (\e, _ => pure (e, Just e))
    []
  where
    draw = do
      mi <- appendNode "input" root
      case mi of
        Just i => registEvent i "change" targetValue
        Nothing => pure ()
      pure []

export
textinput : View String
textinput = textinput' Nothing
