module Hashimoto where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

_↝_ : Set → Set → Set1
A ↝ B = A → B → Set

simple : ∀ {A B} → (A ↝ B) → Set
simple R = ∀ {a b₁ b₂} →  R a b₁ → R a b₂ → b₁ ≡ b₂ 

entire : ∀ {A B} → (A ↝ B) → Set
entire R = ∀ a → ∃ (λ b → R a b)

injective : ∀ {A B} → (A ↝ B) → Set
injective R = ∀ {a₁ a₂ b} → R a₁ b → R a₂ b → a₁ ≡ a₂

surjective : ∀ {A B} → (A ↝ B) → Set
surjective R = ∀ b → ∃ (λ a → R a b)

_˘ : ∀ {A B} → (A ↝ B) → (B ↝ A)
(R ˘) b a = R a b 

fun : ∀ {A B } -> (A ↝ B )
fun f a b = a ≡ b 

-- axiom of choice 

ac : ∀ {A B} → (R : A ↝ B) →
         (∀ a → ∃ (λ b → R a b)) → ∃ {A → B} (λ f → ∀ a → R a (f a))
ac R R-entire = ((λ a → proj₁ (R-entire a)) , λ a → proj₂ (R-entire a))

-- simple ⇒ uniqueness?

uniq : ∀ {A B} → (R : A ↝ B) → simple R → 
          (f₁ : A → B) → (∀ a → R a (f₁ a)) →
          (f₂ : A → B) → (∀ a → R a (f₂ a)) →
             ∀ a → f₁ a ≡ f₂ a
uniq R R-simple f₁ f₁⊆R f₂ f₂⊆R a = R-simple (f₁⊆R a) (f₂⊆R a)

-- lifting a function to a relation

fun : ∀ {A B} → (A → B) → (A ↝ B)
fun f a b = f a ≡ b

{-

Let f : A → B be injective. Does there exist an f⁻¹ such that f⁻¹ ∘ f = id?
Perhaps not so in intuinistic logic with proof irrelevence.

If f is also (provably) surjective, one can pick some g ⊆ f˘ using the
axiom of choice (which takes the proof of surjectivity of f as an
argument) and further prove that g ∘ f = id using injectivity.

-}

inv-sur : ∀ {A B} → (f : A → B) → injective (fun f) → surjective (fun f) →
             ∃ {B → A} (λ f⁻¹ → (∀ a → f⁻¹ (f a) ≡ a))
inv-sur f f-inj f-sur with ac ((fun f) ˘) f-sur
... | (g , fgb≡b) =  (g , λ a → f-inj {g (f a)} {a} {f a} (fgb≡b (f a)) refl)

{-
What if f is not surjective?

Assume that B is some type with decidable equality.
Let P : B → Set be a predicate and let's pick A = Σ B (λ b → P b).
That is, A is the subset of B for which P holds. Let f be proj₁.
Certainly f is injective. Furthermore, assume that A is non-empty.
-}

postulate B : Set
postulate eqB : (b₁ b₂ : B) → (b₁ ≡ b₂) ⊎ (¬ (b₁ ≡ b₂))

postulate pf-irr : (P : B → Set) → ∀ {b} → (p₁ : P b) → (p₂ : P b) → p₁ ≡ p₂

A : (B → Set) → Set
A P = Σ B (λ b → P b)

f : ∀ {P} → A P → B
f = proj₁

f-inj : ∀ {P} → injective (fun (f {P}))  -- we need proof irrelevence to prove this.
f-inj {P} {(.b , Pb₁)} {(.b , Pb₂)} {b} refl refl = cong (λ p → (b , p)) (pf-irr P Pb₁ Pb₂)

{- Assume that inv-sur holds without the surjectivity constraint.
   Therefore, f has an inverse function f⁻¹ : B → A. 
-}

postulate inv : ∀ {A B} → (f : A → B) → injective (fun f) → 
                   ∃ {B → A} (λ f⁻¹ → (∀ a → f⁻¹ (f a) ≡ a))

{-
Given some b, either

 1. P b holds true. In this case f⁻¹ must map b to (b , p) where p 
    is a proof of P b, since f⁻¹ is the left inverse of f.

 2. P b does not hold. In this case f⁻¹, being a total function,
    still has to map b to something. So let us pick some arbitrary 
    value a₀ = (b₀ , p) in A. Certainly, b₀ does not equal b.

However, that means we now have a decision procedure
(P : B → Set) → ∀ b → (P b ⊎ ¬ (P b)). Just compare the left
component of f⁻¹ b with b. If they equal, we return the proof.
Otherwise, having a proof of P b contradicts the inequality.
-}

em : {P : B → Set} → ∀ b → P b ⊎ ¬ (P b)
em {P} b with inv f (f-inj {P})
...      | (f⁻¹ , f⁻¹fa≡a) with inspect (f⁻¹ b) 
...                        | (b' , Pb') with-≡ _          with eqB b b'
em {P} b | (f⁻¹ , f⁻¹fa≡a) | (b' , Pb') with-≡ _          | inj₁ b≡b'  = inj₁ (subst P (sym b≡b') Pb')
em {P} b | (f⁻¹ , f⁻¹fa≡a) | (b' , Pb') with-≡ b'Pb'≡f⁻¹b | inj₂ ¬b≡b' = 
   inj₂ (λ Pb →
           let f⁻¹b≡bPb : f⁻¹ b ≡ (b , Pb)
               f⁻¹b≡bPb = f⁻¹fa≡a (b , Pb)
               bPb≡b'Pb' : (b , Pb) ≡ (b' , Pb')
               bPb≡b'Pb' = sym (trans b'Pb'≡f⁻¹b f⁻¹b≡bPb)
               b≡b' : b ≡ b'
               b≡b' = cong proj₁ bPb≡b'Pb'
           in ¬b≡b' b≡b')

{-
Having f⁻¹ introduces the law of excluded middle. Therefore
it is perhaps not something we can have in intuinistic logic.
-}

{- Nakano san's question: given injective functions f : A → B and g : B → A,
   is there a bijection A → B? 

nakano : {A B : Set} → (f : A → B) → injective (fun f) → (g : B → A) → injective (fun g) →
           ∃ {A → B} (λ h → injective (fun h) × surjective (fun h))
nakano f f-inj g g-inj = 
    (f ∘ g ∘ f , 
     (λ fgfa₁≡b fgfa₂≡b → {!!}) , 
     λ b → {!!})

-}
