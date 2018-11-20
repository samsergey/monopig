# monopig
An example of a monoidal stack machine built from the principles of homomorphisms between a domain (stack-oriented langauge) and different monoidal representations.
The thorough description is given [here](https://habr.com/post/429530/) (in russian)

##File description

All files are selfcontaining independent haskel modules.

- `Monopig1.hs` -- simple stack machine with memory and error handling as EDSL.
- `Monopig2.hs` -- addition of arbitrary logging.
- `Monopig3.hs` -- addition of isomorphism between EDSL and a free algebra representing code. Homomorphisms to pretty printing, arity and memory requariments, some optimisation.
- `Monopig4.hs` -- implementation of monoidal stack machine in Kleisli category. Using `IO` and `[]` monads for effects.
- `Monopig5.hs` -- implementation of monoidal stack machine in Kleisli category. Using `IO` monads and mutable vectors to boost the speed.
