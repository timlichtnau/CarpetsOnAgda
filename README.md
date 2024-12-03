This is a formalization of some ideas I have about Synthetic Diagram Chasing. given any abelian category $\mathcal{A}$, we associate a category of spans, where a morphism $A \rightsquigarrow B$ is given by a span $A \twoheadleftarrow C \to B$ in $\mathcal{A}$, where $A \twoheadleftarrow C$ is epic. We think of such a $A \rightsquigarrow B$ as a way of producing a (possibly non well-defined) term of $B$ if one has given a term of $A$. 
And such a $A \rightsquigarrow B$ comes from an actual morphism $A \to B$, iff $0_A$ is necessarily send to $0_B$.
Instead of formalizing the addition of morphisms in an abelian category we add an axiom, such that the given pointed functions behave like homomorphisms. 
I sketch in here words: In order to show a predicate $A \to \mathsf{Prop}$ holds for all points in all fibers of a pointed function $f : (A,a_0) \to (B,b_0)$, you only need to show it for the whole fiber over the basepoint $\mathrm{ker} f \equiv \mathrm{fib}_f(b_0)$ 
and a single point in each fiber $\mathrm{fib}_f(b) , b : B$, exploiting that every fiber is a $\ker f$-torsor.
