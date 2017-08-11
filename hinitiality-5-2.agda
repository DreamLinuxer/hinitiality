-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-5-2 where
open import Level
open import Base
open import Ch3
open import hinitiality-4
open import hinitiality-5-1

module isind↔ishinit {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  open PAlg {A = A} {B = B}
  open Phinit {A = A} {B = B}

-- Theorem 5.10
  isind→ishinit : ∀ {ℓ ℓ'} {C : Alg {ℓ}} → isind {ℓ' = ℓ'} C → ishinit {ℓ' = ℓ'} C
  isind→ishinit {C = C} Cisind D =
    sec , isind→isPropAlgSec {C = C} Cisind fib sec
    where
    fib : FibAlg C
    fib = ((λ _ → pr₁ D) , (λ pc h → (pr₂ D) ((pr₁ pc) , h)))

    sec : Alghom C D
    sec = Cisind fib

  ishinit→isind : ∀ {ℓ ℓ'} {C : Alg {ℓ}} → ishinit {ℓ' = ℓ ⊔ ℓ'} C → ishinit {ℓ' = ℓ} C → isind {ℓ' = ℓ'} C
  ishinit→isind {C = 𝑪@(C , supc)} Cishinit Cishinitℓ 𝑬@(E , e) = s , funext s'
    where
    𝑬' : Alg
    𝑬' = assAlg {C = 𝑪} 𝑬
    E' = pr₁ 𝑬'
    supe' = pr₂ 𝑬'

    contr : isContr (Alghom 𝑪 𝑬')
    contr = Cishinit 𝑬'

    π₁ : Alghom 𝑬' 𝑪
    π₁ = pr₁ , funext (λ {(x , u) → refl _})

    𝒇 : Alghom 𝑪 𝑬'
    𝒇 = pr₁ contr
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    φ = happly f'

    𝒇₁ : Alghom 𝑪 𝑪
    𝒇₁ = pr₁ ∘ f , funext (λ {(x , u) → pr₁ (pairΣ≡⁻¹ (φ (x , u)))})
    f₁ = pr₁ 𝒇₁
    f₁' = pr₂ 𝒇₁
    φ₁ = happly f₁'

    f₂ : (z : C) → E (f₁ z)
    f₂ z = pr₂ (f z)
    
    𝒊𝒅 : Alghom 𝑪 𝑪
    𝒊𝒅 = id , (funext (λ {(x , u) → refl _}))

    Α : Alg~ {C = 𝑪} {D = 𝑪} 𝒇₁ 𝒊𝒅
    Α = ≃→ (Alghom≃ {C = 𝑪} {D = 𝑪} {f = 𝒇₁} {g = 𝒊𝒅})
           (pr₂ (Cishinitℓ 𝑪) 𝒇₁ ⁻¹ ▪ pr₂ (Cishinitℓ 𝑪) 𝒊𝒅)
    α = pr₁ Α
    α' = pr₂ Α

    s : (x : C) → E x
    s z = transport E (α z) (f₂ z)

    γ : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z}
      → p ▪ q ≡ r ▪ s → r ≡ p ▪ q ▪ s ⁻¹
    γ {p = refl x} {refl .x} {refl .x} {s} α = ap (λ p → refl x ▪ p) (p▪p⁻¹≡reflx _ ⁻¹) ▪ assoc▪ _ _ _ ▪ ap (λ p → p ▪ s ⁻¹) α ⁻¹ 

    claim₁ : (x : A) (u : B x → C) → α (supc (x , u)) ≡ φ₁ (x , u)
                                   ▪ 𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u)
    claim₁ x u = γ (α' (x , u)) ▪ assoc▪ _ _ _ ⁻¹
               ▪ ap (λ p → φ₁ (x , u) ▪ p) (ap (λ q → 𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u) ▪ q) p
               ▪ unit-right _ ⁻¹)
      where
      p : happly (pr₂ 𝒊𝒅) (x , u) ⁻¹ ≡ refl _
      p = ap _⁻¹ (computationΠ _ _)

    claim₂ : (x : A) (u : B x → C) → transport E (φ₁ (x , u)) (f₂ (supc (x , u))) ≡ e (x , f₁ ∘ u) (λ y → f₂ (u y))
    claim₂ x u = ap (λ p → transport E p (f₂ (supc (x , u)))) p ▪ pr₂ (pairΣ≡⁻¹ (φ (x , u)))
      where
      p : φ₁ (x , u) ≡ pr₁ (pairΣ≡⁻¹ (φ (x , u)))
      p = computationΠ _ _

    claim₃ : (x : A) (u : B x → C) → transport E (𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u))
                                                 (e (x , f₁ ∘ u) (λ y → f₂ (u y)))
                                   ≡ e (x , u) (λ y → transport E (α (u y)) (f₂ (u y)))
    claim₃ x u = lem x {t₁ = f₁ ∘ u} {t₂ = u} (funext (λ x → α (u x))) (λ y → f₂ (u y))
               ▪ ap (λ h → e (x , u) (λ y → transport E (h y) (f₂ (u y)))) (compΠ≡ (λ x → α (u x)))
      where
      lem : (a : A) {t₁ t₂ : B a → C} (p : t₁ ≡ t₂) (v : (y : B a) → E (t₁ y))
          → transport E (ap (λ h → supc (a , h)) p) (e (a , t₁) v) ≡ e (a , t₂) (λ y → transport E (happly p y) (v y))
      lem a (refl t) v = refl _

    s' : (pc : P C) → s (supc pc) ≡ e pc (λ x → s ((pr₂ pc) x))
    s' (x , u) = transport E (α (supc (x , u))) (f₂ (supc (x , u)))
              ≡⟨ ap (λ p → transport E p (f₂ (supc (x , u)))) (claim₁ x u) ⟩
                 transport E (φ₁ (x , u) ▪ 𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u))
                             (f₂ (supc (x , u)))
              ≡⟨ transport▪ E (φ₁ (x , u)) _ (f₂ (supc (x , u))) ⁻¹ ⟩
                 transport E (𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u))
                             (transport E (φ₁ (x , u)) (f₂ (supc (x , u))))
              ≡⟨ ap (λ z → transport E (𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u)) z)
                     (claim₂ x u) ⟩
                 transport E (𝒆~ {C = 𝑪} {E = (λ _ → C) , (λ pc h → supc ((pr₁ pc) , h))} α (x , u))
                             (e (x , f₁ ∘ u) (λ y → f₂ (u y)))
              ≡⟨ claim₃ x u ⟩
                 e (x , u) (λ x → s (u x)) ∎
