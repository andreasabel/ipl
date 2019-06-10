2019-05-27

NbE for CBPV via Intutionistic S4
=================================

We work in a cartesian closed category C (×̂, πᵢ, ⟨_,_⟩, ⇒̂, λ, eval)
with weakly extensional coproducts (+̂)

    ?[B] : 0 ⇒ B

    ?[0]  = id   -- extensionality law
    g ∘ ? = ?    -- permutation law

    [ f₁ , f₂ ] ∘ ιᵢ = fᵢ                   -- β-law
    [ ι₁ , ι₂ ]      = id                   -- η-law
    g ∘ [ f₁ , f₂ ]  = [ g ∘ f₁ , g ∘ f₂ ]  -- π-law (permutation law)

and a strong monad (◇, η, μ, t)

    μ ∘ η   = id
    μ ∘ ◇ η = id
    μ ∘ ◇ μ = μ ∘ μ

and a monoidal comonad □

    ε : □ A ⇒ A
    δ : □ A ⇒ □ (□ A)

    ε   ∘ δ = id
    □ ε ∘ δ = id
    □ δ ∘ δ = δ ∘ δ

    m[1]   : 1 ⇒ □ 1
    m[A×̂B] : □ A ×̂ □ B ⇒ □ (A ×̂ B)
.

Morphisms are f : A ⇒ B while we reserve → for the meta-language.

Recall strength t (from the right)

    t : ◇ A ×̂ B ⇒ ◇ (A ×̂ B)

    t ∘ (η × id) = η

and the definition of the Kleisli extension:

    _† : (A ⇒ ◇ B) → (◇ A ⇒ ◇ B)
    f † = μ ∘ ◇ f

We obtain strong functoriality, i.e. the morphism

    ◇̂ : □ (A ⇒̂ B) ×̂ ◇ A ⇒ ◇ B
    ◇̂ = ◇ (eval ∘ (ε × id)) ∘ t

NB: The curried version is

  ◇̂c : □ (A ⇒̂ B) ⇒ (◇ A ⇒̂ ◇ B)
  ◇̂c = λ ◇̂

Negative objects
----------------

Definition: An object N is called negative (or monadic) if the monadic unit

    η : N ⇒ ◇ N

for N has a left inverse

    run[N] : ◇ N ⇒ N
    run[N] ∘ η[N] = id[N]

This allows us to define

    bind : (A ⇒ N) → (◇ A ⇒ N)
    bind f = run ∘ ◇ f

  NB: bind' f = run ∘ (η ∘ f) †
              = run ∘ (η ∘ f) † = run ∘ μ ∘ (◇ (η ∘ f))
              = run ∘ μ ∘ ◇ η ∘ ◇ f
              = run ∘ ◇ f

which generalizes the Kleisli extension _† from ◇ B to N.

We also get the strong bind

    b̂ind : □ (A ⇒̂ N) ×̂ ◇ A ⇒ N
    b̂ind = run ∘ ◇̂

NB: the curried version is

  b̂indc : □ (A ⇒̂ N) ⇒ (◇ A ⇒̂ N)
  b̂indc = λ (run ∘ λ⁻¹ ◇̂c)

Lemma: Finite products of negative objects are negative.

    run[1] : ◇ 1 ⇒ 1
    run[1] = !

    run[N₁×̂N₂] : ◇ (N₁ ×̂ N₂) ⇒ N₁ ×̂ N₂
    run[N₁×̂N₂] = ⟨run ∘ ◇ π₁ , run ∘ ◇ π₂⟩

    run ∘ η = ⟨run ∘ ◇ π₁ , run ∘ ◇ π₂⟩ ∘ η
            = ⟨run ∘ ◇ π₁ ∘ η , run ∘ ◇ π₂ ∘ η⟩
            = ⟨run ∘ η ∘ π₁ , run ∘ η ∘ π₂⟩
            = ⟨π₁ , π₂⟩
            = id                                   -- η for ×

This generalizes to limits:

  run[lim N] : ◇ (lim N) ⇒ lim N
  run[lim N] = ⟨run ∘ ◇ πᵢ⟩ᵢ

where

- i ranges over the objects of the index category I
- N is a functor from I into the subcategory of negative objects
- lim N is the tip of the cone
- πᵢ : lim N → Nᵢ are the top-down edges of the cone
- ⟨f⟩ denotes the unique morphism constructed from the fᵢ : ◇ (lim N) ⇒ Nᵢ

Lemma: The exponential over a negative codomain is negative.

    run[A⇒̂N] = λ run'
    run' : ◇ (A ⇒̂ N) ×̂ A ⇒ N
    run' = run ∘ ◇ eval ∘ t

    run ∘ η = λ (run ∘ ◇ eval ∘ t) ∘ η         -- definition
            = λ (run ∘ ◇ eval ∘ t ∘ (η × id))  -- universality of λ
            = λ (run ∘ ◇ eval ∘ η)             -- law of strength
            = λ (run ∘ η ∘ eval)               -- naturality of η
            = λ eval                           -- N negative
            = id                               -- extensionality of exponentials

Since ◇ A is trivially negative (run[◇A] = μ), we get a grammar for negative objects:

    N ::= 1 | N₁ ×̂ N₂ | A ⇒ N | ◇ A

Positive objects
----------------

Definition:  An object P is called positive (or comonadic) if the
comonadic unit

    ε : □ P ⇒ P

has an right inverse

    mon : P ⇒ □ P
    ε ∘ mon = id

this allows us to define

    thunk : (P ⇒ B) → P ⇒ □ B
    thunk f = □ f ∘ mon

Lemma: positive objects are closed under coproducts.

    mon[0] : 0 ⇒ □ 0
    mon[0] = ?[□0]

      ε ∘ mon = ε ∘ ?[□0] = ?[0] = id[0]

    mon[P₁+P₂] : P₁ + P₂ ⇒ □ (P₁ + P₂)
    mon[P₁+P₂] = [ □ ι₁ ∘ mon[P₁] ,  □ ι₂ ∘ mon[P₂] ]

      ε ∘ mon = ε ∘ [ □ ι₁ ∘ mon[P₁] ,  □ ι₂ ∘ mon[P₂] ]      -- definition
              = [ ε ∘ □ ι₁ ∘ mon[P₁] ,  ε ∘ □ ι₂ ∘ mon[P₂] ]  -- permutation law for case
              = [ ι₁ ∘ ε ∘ mon[P₁] ,  ι₂ ∘ ε ∘ mon[P₂] ]      -- naturality of ε
              = [ ι₁ ∘ id[P₁] ,  ι₂ ∘ id[P₂] ]                -- positivity of Pᵢ
              = [ ι₁ ,  ι₂ ]                                  -- identity
              = id                                           -- η-law for sums

Lemma: positive objects are closed under products, thanks to the monoidality of the comonad.

    mon[P₁×P₂] : P₁ × P₂ ⇒ □ (P₁ × P₂)
    mon[P₁×P₂] = m[P₁×P₂] ∘ ⟨ mon[P₁] ,  mon[P₂] ⟩

Since □ A is trivially positive (mon[□P] = δ), the following grammar produces positive objects:

    P ::= 0 | P₁ + P₂ | 1 | P₁ × P₂ | □ A
