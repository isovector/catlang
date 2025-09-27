-- type tape = char * (string * string)
moveRight =
  tape ->
    c <- proj1 -< tape
    more <- proj2 -< tape
    before <- proj1 -< more
    after <- proj2 -< more
    unconsed <- uncons -< after
    case unconsed of
      inl z ->
        c1 <- empty -< (c)
        before1 <- cons -< (c, before)
        id -< (c1, before1, after)
      inr res ->
        c1 <- proj1 -< res
        after1 <- proj2 -< res
        before1 <- cons -< (c, before)
        id -< (c1, before1, after1)

