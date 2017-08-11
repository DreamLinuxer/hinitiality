-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-5-1 where
open import Level
open import Base
open import Ch3
open import hinitiality-4

module Phinit {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  open PAlg {A = A} {B = B}

-- Definition 5.1
  isind : ∀ {ℓ ℓ'} (C : Alg {ℓ}) → Set _
  isind {ℓ' = ℓ'} C = (E : FibAlg {ℓ' = ℓ'} C) → AlgSec C E

  ishinit : ∀ {ℓ ℓ'} (C : Alg {ℓ}) → Set _
  ishinit {ℓ' = ℓ'} C = (D : Alg {ℓ = ℓ'}) → isContr (Alghom C D)

-- Proposition 5.2
  hinit-uniqiso : ∀ {ℓ} (C : Alg {ℓ}) (D : Alg {ℓ})
                → ishinit {ℓ' = ℓ} C × ishinit {ℓ' = ℓ} D
                → isContr (AlgEquiv {C = C} {D = D})
  hinit-uniqiso 𝑪 𝑫 (Cishinit , Dishinit) = ≃isContr (isProp→isContra (isalgequivIsProp , algeq)) eq
    where
    algeq : isalgequiv {C = 𝑪} {D = 𝑫} (pr₁ (Cishinit 𝑫))
    algeq with (Dishinit 𝑪)
    ... | g , _ = (g , pr₂ (Cishinit 𝑪) _ ⁻¹ ▪ pr₂ (Cishinit 𝑪) _)
                , (g , pr₂ (Dishinit 𝑫) _ ⁻¹ ▪ pr₂ (Dishinit 𝑫) _)
    
    eq : isalgequiv {C = 𝑪} {D = 𝑫} (pr₁ (Cishinit 𝑫)) ≃ AlgEquiv {C = 𝑪} {D = 𝑫}
    eq = isContrA→ΣPx≃Pa _ (isalgequiv {C = 𝑪} {D = 𝑫}) (Cishinit 𝑫) ⁻¹≃

-- Proposition 5.3
  module _ {ℓ ℓ'} {C : Alg {ℓ}} {Cisind : isind {ℓ' = ℓ'} C} where
    elim : (E : pr₁ C → Set ℓ')
         → (e : (pc : P (pr₁ C)) → ((y : B (pr₁ pc)) → E (pr₂ pc y)) → E (pr₂ C pc))
         → ((z : pr₁ C) → E z)
    elim E e = pr₁ (Cisind (E , e))

    comp : (E : pr₁ C → Set ℓ')
         → (e : (pc : P (pr₁ C)) → ((y : B (pr₁ pc)) → E (pr₂ pc y)) → E (pr₂ C pc))
         → (pc : P (pr₁ C)) → elim E e (pr₂ C pc) ≡ e pc (λ y → elim E e (pr₂ pc y))
    comp E e = happly (pr₂ (Cisind (E , e)))

-- Proposition 5.4
    η : (E : pr₁ C → Set ℓ')
      → (e : (pc : P (pr₁ C)) → ((y : B (pr₁ pc)) → E (pr₂ pc y)) → E (pr₂ C pc))
      → (f : (z : pr₁ C) → E z)
      → (ϕ : (pc : P (pr₁ C)) → f (pr₂ C pc) ≡ e pc (λ y → f (pr₂ pc y)))
      → (z : pr₁ C) → f z ≡ elim E e z
    η E e f ϕ = elim T t
      where
      T : pr₁ C → Set _
      T z = f z ≡ elim E e z
      t = λ pc v → ϕ pc ▪ ap (e pc) (funext (λ y → v y)) ▪ comp E e pc ⁻¹

    η' : (E : pr₁ C → Set ℓ')
       → (e : (pc : P (pr₁ C)) → ((y : B (pr₁ pc)) → E (pr₂ pc y)) → E (pr₂ C pc))
       → (f : (z : pr₁ C) → E z)
       → (ϕ : (pc : P (pr₁ C)) → f (pr₂ C pc) ≡ e pc (λ y → f (pr₂ pc y)))
       → (pc : P (pr₁ C)) → η E e f ϕ (pr₂ C pc) ▪ comp E e pc ≡ ϕ pc ▪ ap (e pc) (funext (λ y → η E e f ϕ (pr₂ pc y)))
    η' E e f ϕ pc = η E e f ϕ (pr₂ C pc) ▪ comp E e pc
                 ≡⟨ ap (λ p → p ▪ comp E e pc) (comp T t pc) ▪ assoc▪ _ _ _ ⁻¹ ⟩
                    ϕ pc ▪ ap (e pc) (funext (λ y → η E e f ϕ (pr₂ pc y))) ▪ (comp E e pc ⁻¹ ▪ comp E e pc)
                 ≡⟨ ap (λ p → ϕ pc ▪ ap (e pc) (funext (λ y → η E e f ϕ (pr₂ pc y))) ▪ p) (p⁻¹▪p≡refly _)
                  ▪ unit-right _ ⁻¹ ⟩
                    ϕ pc ▪ ap (e pc) (funext (λ y → η E e f ϕ (pr₂ pc y))) ∎
      where
      T : pr₁ C → Set _
      T z = f z ≡ elim E e z
      t = λ pc v → ϕ pc ▪ ap (e pc) (funext (λ y → v y)) ▪ comp E e pc ⁻¹

-- Corollary 5.5
  isind→isPropAlgSec : ∀ {ℓ ℓ'} {C : Alg {ℓ}} (CisInd : isind {ℓ' = ℓ'} C)
                     → (E : FibAlg {ℓ' = ℓ'} C)
                     → (f g : AlgSec C E) → f ≡ g
  isind→isPropAlgSec {C = 𝑪@(C , supc)} CisInd 𝑬@(E , e) 𝒇@(f , f') 𝒈@(g , g') =
    ≃← (AlgSec≃ {C = 𝑪} {E = 𝑬}) ((λ x → ηf x ▪ ηg x ⁻¹) , α)
    where
    ηf = η {C = 𝑪} {Cisind = CisInd} E e f (happly f')
    ηg = η {C = 𝑪} {Cisind = CisInd} E e g (happly g')
    ηf' = η' {C = 𝑪} {Cisind = CisInd} E e f (happly f')
    ηg' = η' {C = 𝑪} {Cisind = CisInd} E e g (happly g')
    com = comp {C = 𝑪} {Cisind = CisInd} E e

    γ : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z}
      → p ▪ q ≡ r ▪ s → p ▪ q ▪ s ⁻¹ ≡ r
    γ {p = refl x} {refl .x} {refl .x} {s} α = ap (λ q → q ▪ s ⁻¹) α ▪ assoc▪ _ _ _ ⁻¹
                                             ▪ ap (λ q → refl x ▪ q) (p▪p⁻¹≡reflx _)

    γ' : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ x₄ x₅ : A}
       → {p₁ : x₁ ≡ x₂} {p₂ : x₃ ≡ x₂} {p₃ : x₂ ≡ x₄} {p₄ : x₄ ≡ x₅}
       → p₁ ▪ p₂ ⁻¹ ▪ (p₂ ▪ p₃ ▪ p₄) ≡ p₁ ▪ p₃ ▪ p₄
    γ' {p₁ = refl x} {refl .x} {refl .x} {refl .x} = refl (refl x)

    γ'' : ∀ {ℓ} {A : Set ℓ} {w x y : A} {p p' : w ≡ x} {q q' : x ≡ y}
        → (α : p ≡ p') (β : q ≡ q') → p ▪ q ≡ p' ▪ q'
    γ'' (refl p) (refl q) = refl _

    γ''' : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ x₄ x₅ : A}
         → {p₁ : x₁ ≡ x₂} {p₂ : x₂ ≡ x₃} {p₃ : x₄ ≡ x₃} {p₄ : x₃ ≡ x₅}
         → (p₁ ▪ p₂ ▪ p₃ ⁻¹) ▪ (p₃ ▪ p₄) ≡ p₁ ▪ p₂ ▪ p₄
    γ''' {p₁ = refl x} {refl .x} {refl .x} {refl .x} = refl (refl x)

    ε : ∀ {f g h : (x : C) → E x} {ηf : f ≡ h} {ηg : g ≡ h}
      → (x : A) (u : B x → C)
      → (funext (λ y → happly ηf (u y) ▪ happly ηg (u y) ⁻¹))
      ≡ (funext (λ y → happly ηf (u y))) ▪ (funext (λ y → happly ηg (u y)) ⁻¹)
    ε {ηf = refl f} {refl .f} x u = unit-right _
                                  ▪ ap (λ p → funext (λ y → refl (f (u y))) ▪ p ⁻¹) (refΠ _)

    α : (pc : P C) → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (λ z → ηf z ▪ ηg z ⁻¹) pc
                   ≡ ηf (supc pc) ▪ ηg (supc pc) ⁻¹ ▪ happly g' pc
    α (x , u) = happly f' (x , u) ▪ ap (e (x , u)) (funext (λ y → ηf (u y) ▪ ηg (u y) ⁻¹))
             ≡⟨ γ'' (γ (ηf' (x , u)) ⁻¹)
                    ( ap (ap (e (x , u)))
                         ( ap (λ α → funext (λ y → α (u y) ▪ ηg (u y) ⁻¹)) (compΠ≡ ηf ⁻¹)
                         ▪ ap (λ α → funext (λ y → (happly (funext ηf)) (u y) ▪ α (u y) ⁻¹)) (compΠ≡ ηg ⁻¹)
                         ▪ ε x u
                         ▪ ap (λ α → funext (λ y → (happly (funext ηf)) (u y)) ▪ (funext (λ y → α (u y)) ⁻¹)) (compΠ≡ ηg)
                         ▪ ap (λ α → funext (λ y → α (u y)) ▪ (funext (λ y → ηg (u y)) ⁻¹)) (compΠ≡ ηf))
                    ▪ ap▪ _ _ _ _ _ _
                    ▪ ap (λ p → ap (e (x , u)) (funext (λ y → ηf (u y))) ▪ p) (ap⁻¹ _ _ _ _)) ⟩
                (ηf (supc (x , u)) ▪ com (x , u) ▪ ap (e (x , u)) (funext (λ y → ηf (u y))) ⁻¹) ▪
                (ap (e (x , u)) (funext (λ y → ηf (u y))) ▪ ap (e (x , u)) (funext (λ y → ηg (u y))) ⁻¹)
             ≡⟨ γ''' ⟩
                ηf (supc (x , u)) ▪ com (x , u) ▪ ap (e (x , u)) (funext (λ y → ηg (u y))) ⁻¹
             ≡⟨ γ' ⁻¹ ⟩
                ηf (supc (x , u)) ▪ ηg (supc (x , u)) ⁻¹ ▪
                (ηg (supc (x , u)) ▪ com (x , u) ▪ ap (e (x , u)) (funext (λ y → ηg (u y))) ⁻¹)
             ≡⟨ ap (λ p → ηf (supc (x , u)) ▪ ηg (supc (x , u)) ⁻¹ ▪ p) (γ (ηg' (x , u))) ⟩
                ηf (supc (x , u)) ▪ ηg (supc (x , u)) ⁻¹ ▪ happly g' (x , u) ∎

  isindisProp : ∀ {ℓ ℓ'} {C : Alg {ℓ}} → isProp (isind {ℓ' = ℓ'} C)
  isindisProp {C = C} Cisind _ = ΠisProp (isind→isPropAlgSec {C = C} Cisind) _ _

-- Lemma 5.7
  hinit→isequiv[sup] : ∀ {ℓ} {C : Alg {ℓ}} → ishinit C → ishinit C → isequiv (pr₂ C)
  hinit→isequiv[sup] {C = 𝑪} Cishinit₁ Cishinit₂ = qinv→isequiv (t , p , q)
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪

    PC : Alg
    PC = (P C) , (𝑷 supc)

    contr : isContr (Alghom 𝑪 PC)
    contr = Cishinit₁ PC

    t = pr₁ (pr₁ contr)
    t' = pr₂ (pr₁ contr)

    sup∘t : Alghom 𝑪 𝑪
    sup∘t = (supc ∘ t) , (ap (λ h → supc ∘ h) t')

    p = happly (ap pr₁ (pr₂ (Cishinit₂ 𝑪) sup∘t ⁻¹ ▪ pr₂ (Cishinit₂ 𝑪) (idAlg {C = 𝑪})))
    q = happly (t' ▪ ϕ t supc ⁻¹ ▪ ap 𝑷 (funext p) ▪ ϕid)

-- Proposition 5.8
  module _ {ℓ ℓ'} {C : Alg {ℓ}} {Cishinit : ishinit {ℓ' = ℓ'} C} where
    rec : (D : Set ℓ') (supd : P D → D) → (z : pr₁ C) → D
    rec D supd = pr₁ (pr₁ (Cishinit (D , supd)))

    β : (D : Set ℓ') (supd : P D → D)
      → (pc : P (pr₁ C)) → rec D supd (pr₂ C pc) ≡ supd (𝑷 (rec D supd) pc)
    β D supd = happly (pr₂ (pr₁ (Cishinit (D , supd))))

    ηz : (D : Set ℓ') (supd : P D → D)
       → (f : pr₁ C → D) (ϕ : (pc : P (pr₁ C)) → f (pr₂ C pc) ≡ supd (𝑷 f pc))
       → (z : pr₁ C) → f z ≡ rec D supd z
    ηz D supd f ϕ = happly (pr₁ (pairΣ≡⁻¹ ((pr₂ (Cishinit (D , supd))) (f , funext ϕ))) ⁻¹)

    ηz' : (D : Set ℓ') (supd : P D → D)
        → (f : pr₁ C → D) (ϕ : (pc : P (pr₁ C)) → f (pr₂ C pc) ≡ supd (𝑷 f pc))
        → (pc : P (pr₁ C)) → ηz D supd f ϕ (pr₂ C pc) ▪ β D supd pc
                           ≡ ϕ pc ▪ ap (λ h → supd (𝑷 h pc)) (funext (ηz D supd f ϕ))
    ηz' D supd f ϕ pc = happly (p ⁻¹) (supc pc) ▪ happly recf' pc
                    ≡⟨ γ₂ (γ (p ⁻¹) (supc pc)) (refl _) ▪ γ₃' ⁻¹ ⟩
                       (ap (λ h → h (supc pc)) (p ⁻¹) ▪ happly recf' pc ▪ ap (λ h → supd (𝑷 h pc)) p) ▪ ap (λ h → supd (𝑷 h pc)) p ⁻¹
                    ≡⟨ γ₂ (γ' pc) (ap⁻¹ _ _ _ _ ⁻¹ ▪ ap (λ p → ap (λ h → supd (𝑷 h pc)) p) (uniqΠ (p ⁻¹))) ⟩
                       ϕ pc ▪ ap (λ h → supd (𝑷 h pc)) (funext (happly (p ⁻¹))) ∎
      where
      supc = pr₂ C
      ηD = ηz D supd f ϕ
      βD = β D supd
      recf : pr₁ C → D
      recf = pr₁ (pr₁ (Cishinit (D , supd)))
      recf' : recf ∘ supc ≡ supd ∘ 𝑷 recf
      recf' = pr₂ (pr₁ (Cishinit (D , supd)))
      p : recf ≡ f
      p = (pr₁ (pairΣ≡⁻¹ ((pr₂ (Cishinit (D , supd))) (f , funext ϕ))))
      q : (p *) recf' ≡ funext ϕ
      q = (pr₂ (pairΣ≡⁻¹ ((pr₂ (Cishinit (D , supd))) (f , funext ϕ))))
      r : (ap (λ h → h ∘ supc) p) ⁻¹ ▪ recf' ▪ ap (λ h → supd ∘ 𝑷 h) p ≡ funext ϕ
      r = transport[x↦fx≡gx] _ _ p recf' ⁻¹ ▪ q

      γ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
        → (p : f ≡ g) (x : A) → happly p x ≡ ap (λ f → f x) p
      γ (refl f) x = refl (refl (f x))
      
      γ₂ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p q : x ≡ y} {r s : y ≡ z}
         → p ≡ q → r ≡ s → p ▪ r ≡ q ▪ s
      γ₂ (refl p) (refl q) = refl _

      γ₃ : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p q : w ≡ x} {r s : x ≡ y} {t u : y ≡ z}
         → p ≡ q → r ≡ s → t ≡ u → p ▪ r ▪ t ≡ q ▪ s ▪ u
      γ₃ (refl p) (refl q) (refl t) = refl _

      γ₃' : ∀ {ℓ} {A : Set ℓ} {w x y : A} {p : w ≡ x} {q : x ≡ y}
         →  (p ▪ q) ▪ q ⁻¹ ≡ p
      γ₃' {p = refl x} {refl .x} = refl (refl x)

      γ' : (pc : P (pr₁ C)) → (ap (λ h → h (supc pc)) (p ⁻¹) ▪ happly recf' pc ▪ ap (λ h → supd (𝑷 h pc)) p) ≡ ϕ pc
      γ' pc = ((ap (λ h → h (supc pc)) (p ⁻¹)) ▪ happly recf' pc ▪ ap (λ h → supd (𝑷 h pc)) p)
           ≡⟨ γ₃ ((ap∘ (λ h → h ∘ supc) (λ f₁ → f₁ pc) _ _ (p ⁻¹) ⁻¹ ▪ ap (ap (λ f₁ → f₁ pc)) (ap⁻¹ _ _ _ _)))
                 (refl _) (ap∘ _ _ _ _ _ ⁻¹) ⟩
              ap (λ f₁ → f₁ pc) (ap (λ h → h ∘ supc) p ⁻¹)
            ▪ happly recf' pc
            ▪ ap (λ f₁ → f₁ pc) (ap (λ h → supd ∘ 𝑷 h) p)
           ≡⟨ γ₃ (refl _) (γ recf' pc) (refl _)
            ▪ ap (λ p' → p' ▪ ap (λ f₁ → f₁ pc) (ap (λ h → supd ∘ 𝑷 h) p)) (ap▪ (λ f₁ → f₁ pc) _ _ _ _ _ ⁻¹)
            ▪ ap▪ (λ f₁ → f₁ pc) _ _ _ _ _ ⁻¹ ⟩
              ap (λ f₁ → f₁ pc) ((ap (λ h → h ∘ supc) p) ⁻¹ ▪ recf' ▪ ap (λ h → supd ∘ 𝑷 h) p)
           ≡⟨ ap (λ p₁ → ap (λ f → f pc) p₁) r ▪ γ (funext ϕ) pc ⁻¹ ⟩
              happly (funext ϕ) pc
           ≡⟨ computationΠ _ _ ⟩
              ϕ pc ∎
