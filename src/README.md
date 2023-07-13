# Formalization of Small Ramsey Numbers Using Lean 
This ongoing project is a joint work by David Narvez, Congyan (Cruise) Song, and Ningxin Zhang. We are using interatvie theorm prover Lean to formalize theories regrading small Ramsey numbers.
## Van der Waerden's theorem
The statement of the theorem is at [here](https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem). 

Our major contributions so far were formalizing W(2,3) = 9, see ```vdw.lean```, in which we designed a pick tactic to pick distinct elements from a multiset (based on Generalized Pigeonhole Principle), see ```pick_tactic.lean```.
## Ramsey Theory 
This part is under construction. 

## Usage
First, install Lean 3 following from [here](https://leanprover.github.io/download/).

Then clone the project onto your computer e.g. with ```git clone git@github.com:cruisesong7/formal_proof.git```.