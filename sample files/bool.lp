let True = \x y.x
let False = \x y.y  // == 0
let and = \x y.x y False
let or = \x y.x True y
let not = \x.x False True
let xor = \x y.x (not y) y
let eq = \x y.x y (not y)  // == not xor
let imply = \x y.x y True

let mid && = and
let mid || = or
let ~ = not
let mid ^ = xor
let mid ?= = eq
let mid -> = imply

// a function used to work with enumerating True and False
// p stands for a proposition waiting for enumerating
// r stands for the relation between the enumerated propositions
// f stands for the function to apply to the proposition been applied
let enum = \r f p.r (f (p True)) (f (p False))

let de_morgan = \x y.(~ (x && y)) ?= (~ x) || (~ y)

%rv
// prove de_morgan by computation -- `and` all possible values
de_morgan False False \
&& \
de_morgan False True \
&& \
de_morgan True False \
&& \
de_morgan True True
