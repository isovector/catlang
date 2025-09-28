-- type tape = char * (string * string)

moveRight : Char * (String * String) -> Char * (String * String)
moveRight =
  tape ->
    let (c, (before, after)) = tape
    unconsed <- uncons -< after
    case unconsed of
      inl z ->
        c1 <- empty -< c
        before1 <- cons -< (c, before)
        id -< (c1, (before1, after))
      inr (c2, after1) ->
        before1 <- cons -< (c, before)
        id -< (c2, (before1, after1))
