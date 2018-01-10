Printing for types isn't quite right.
(a -> b) -> c currently prints as a -> b -> c
but it shouldnt!
a -> (b -> c) prints as a -> b -> c which we want to preserve.
