// This file contains some common definitions that are used frequently

let id = \x.x
// function composition
let mid . = \x y z.x (y z)
let mid |> = \x f.f x

// pairs
let pair = \x y p.p x y
let fst = \p.p (\x y.x)
let snd = \p.p (\x y.y)
