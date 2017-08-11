-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-4 where
open import Level
open import Base
open import Ch3
open import Ch4
open import Ex2
import hinitiality-2 as H2

module PAlg {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  P : ∀ {ℓ} (C : Set ℓ) → Set _
  P C = Σ[ x ∈ A ] (B x → C)

  𝑷 : ∀ {ℓ ℓ'} {C : Set ℓ} {D : Set ℓ'} (f : C → D) → P C → P D
  𝑷 f pc = x , f ∘ u
    where
    x = pr₁ pc
    u = pr₂ pc

  ϕ : ∀ {ℓ ℓ' ℓ''} {C : Set ℓ} {D : Set ℓ'} {E : Set ℓ''} (f : C → D) (g : D → E)
    → 𝑷 (g ∘ f) ≡ 𝑷 g ∘ 𝑷 f
  ϕ f g = funext (λ {(x , u) → refl _})

  ϕid : ∀ {ℓ} {C : Set ℓ} → 𝑷 {C = C} {D = C} id ≡ id
  ϕid = funext (λ {(x , u) → refl _})

-- Definition 4.1
  Alg : ∀ {ℓ} → Set _
  Alg {ℓ} = Σ[ C ∈ Set ℓ ] (P C → C)

-- Definition 4.2
  isalghom : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f : pr₁ C → pr₁ D) → Set _
  isalghom {C = C} {D} f = f ∘ supc ≡ supd ∘ 𝑷 f
    where
    supc = pr₂ C
    supd = pr₂ D

  Alghom : ∀ {ℓ ℓ'} (C : Alg {ℓ}) (D : Alg {ℓ'}) → Set _
  Alghom C D = Σ[ f ∈ (pr₁ C → pr₁ D) ] isalghom {C = C} {D} f

  idAlg : ∀ {ℓ} {C : Alg {ℓ}} → Alghom C C
  idAlg {C = C} = id , ap (λ h → pr₂ C ∘ h) (ϕid ⁻¹)

  _∘P_ : ∀ {ℓ ℓ' ℓ''} {C : Alg {ℓ}} {D : Alg {ℓ'}} {E : Alg {ℓ''}}
       → Alghom D E → Alghom C D → Alghom C E
  _∘P_ {E = E} (g , g') (f , f') = (g ∘ f) , ap (λ h → g ∘ h) f' ▪ ap (λ h → h ∘ 𝑷 f) g' ▪ ap (λ h → pr₂ E ∘ h) (ϕ f g) ⁻¹

-- Definition 4.5
  FibAlg : ∀ {ℓ ℓ'} (C : Alg {ℓ}) → Set _
  FibAlg {ℓ' = ℓ'} C = Σ[ E ∈ (pr₁ C → Set ℓ') ] ((pc : P (pr₁ C)) → ((y : B (pr₁ pc)) → E ((pr₂ pc) y)) → E (pr₂ C pc))

  assAlg : ∀ {ℓ ℓ'} {C : Alg {ℓ}} (E : FibAlg {ℓ' = ℓ'} C) → Alg
  assAlg {C = C} E = (Σ[ z ∈ pr₁ C ] (pr₁ E z)) , (λ {(x , u) → (pr₂ C (x , pr₁ ∘ u)) , pr₂ E (x , (pr₁ ∘ u)) (λ y → pr₂ (u y))})

-- Definition 4.6
  𝒆 : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} (f : (x : pr₁ C) → pr₁ E x)
    → (pc : P (pr₁ C)) → pr₁ E (pr₂ C pc)
  𝒆 {E = E} f pc = (pr₂ E) pc (λ x → f (u x))
    where
    u = pr₂ pc

  AlgSec : ∀ {ℓ ℓ'} (C : Alg {ℓ}) (E : FibAlg {ℓ' = ℓ'} C) → Set _
  AlgSec C E = Σ[ f ∈ ((x : pr₁ C) →  (pr₁ E x)) ] (λ pc → f (pr₂ C pc)) ≡ 𝒆 {C = C} {E = E} f

  𝒆~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} {f g : (x : pr₁ C) → pr₁ E x}
     → (α : f ~ g) → 𝒆 {C = C} {E = E} f ~ 𝒆 {C = C} {E = E} g
  𝒆~ {E = E} {f} {g} α pc = ap (pr₂ E pc) (funext (λ x → α (u x)))
    where
    x = pr₁ pc
    u = pr₂ pc

  AlgSec~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C}
          → (f g : AlgSec C E) → Set _
  AlgSec~ {C = 𝑪} {𝑬} 𝒇 𝒈 = Σ[ α ∈ (f ~ g) ] ((λ {pc → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} α pc})
                                            ~ (λ {pc → α (supc pc) ▪ happly g' pc}))
    where
    C = pr₁ 𝑪
    E = pr₁ 𝑬
    supc = pr₂ 𝑪
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

  Alg~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f g : Alghom C D) → Set _
  Alg~ {ℓ} {ℓ'} {𝑪} {𝑫} = AlgSec~ {C = 𝑪} {E = (λ _ → D) , (λ pc h → supd ((pr₁ pc) , h))}
    where
    D = pr₁ 𝑫
    supd = pr₂ 𝑫

--Lemma 4.8
  AlgSec≃ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} {f g : AlgSec C E}
          → f ≡ g ≃ AlgSec~ {C = C} {E = E} f g
  AlgSec≃ {C = 𝑪} {𝑬} {𝒇} {𝒈} = 𝒇 ≡ 𝒈
                             ≃⟨ Σ≃ ⟩
                                Σ[ p ∈ (f ≡ g) ] transport (λ h → (λ pc → h (supc pc)) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h) p f' ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ r → r ≡ g') (eq₁ p f'))) ⟩
                                Σ[ p ∈ (f ≡ g) ] ap (λ h → (λ pc → h (supc pc))) p  ⁻¹ ▪ f' ▪ ap (𝒆 {C = 𝑪} {E = 𝑬}) p ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ s → s  ≡ g') (assoc▪ _ _ _ ⁻¹) ▪ eq₂ )) ⟩
                                Σ[ p ∈ (f ≡ g) ] f' ▪ ap (𝒆 {C = 𝑪} {E = 𝑬}) p ≡ ap (λ h → (λ pc → h (supc pc))) p ▪ g'
                             ≃⟨ ≃→Σ≃ (λ p → eq₃ p f' g') ⟩
                                Σ[ p ∈ (f ≡ g) ] ((λ pc → happly f' pc ▪ (𝒆~ {C = 𝑪} {E = 𝑬} (happly p) pc))
                                                ~ (λ pc → (happly p) (supc pc) ▪ happly g' pc))
                             ≃⟨ ≃→≃Σ (happly , funextentionality) (λ p → ref≃) ⟩
                                AlgSec~ {C = 𝑪} {E = 𝑬} 𝒇 𝒈 ∎≃
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪
    E = pr₁ 𝑬
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

    eq₁ : {f g : (x : C) → E x} (p : f ≡ g) (f' : (λ pc → f (supc pc)) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f)
        → transport (λ h → (λ pc → h (supc pc)) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h) p f'
        ≡ ap (λ h pc → h (supc pc)) p ⁻¹ ▪ f' ▪ ap (𝒆 {C = 𝑪} {E = 𝑬}) p
    eq₁ (refl x) f' = unit-left _ ▪ unit-right _

    eq₂ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p : y ≡ x} {q : y ≡ z} {r : x ≡ z}
        → (p ⁻¹ ▪ q ≡ r) ≡ (q ≡ p ▪ r)
    eq₂ {p = refl x} {refl .x} {r} = ap (λ s → refl x ≡ s) (unit-left _)

    eq₃ : {f g : (x : C) → E x} (p : f ≡ g)
        → (f' : (λ pc → f (supc pc)) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f)
        → (g' : (λ pc → g (supc pc)) ≡ 𝒆 {C = 𝑪} {E = 𝑬} g)
        → (f' ▪ ap (𝒆 {C = 𝑪} {E = 𝑬}) p ≡ ap (λ h pc → h (supc pc)) p ▪ g')
        ≃ ((λ pc → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (happly p) pc) ~ (λ pc → happly p (supc pc) ▪ happly g' pc))
    eq₃ {f = f} {g = .f} (refl .f) f' g' =
        f' ▪ refl (𝒆 {C = 𝑪} {E = 𝑬} f) ≡ refl (λ pc → f (supc pc)) ▪ g'
     ≃⟨ idtoeqv (ap (λ p → p ≡ refl (λ pc → f (supc pc)) ▪ g') (unit-right f' ⁻¹)) ⟩
        f' ≡ refl (λ pc → f (supc pc)) ▪ g'
     ≃⟨ idtoeqv (ap (λ p → f' ≡ p) (unit-left g' ⁻¹)) ⟩
        f' ≡ g'
     ≃⟨ ap happly , ap≡ happly funextentionality ⟩
        happly f' ≡ happly g'
     ≃⟨ happly , funextentionality ⟩
        happly f' ~ happly g'
     ≃⟨ idtoeqv (ap (λ h → h ~ happly g')
                    (funext (λ {(x , u) → unit-right _
                                        ▪ ap (λ p → happly f' (x , u) ▪ p) (ap (ap (pr₂ 𝑬 (x , u))) (refΠ (λ x₁ → f (u x₁))))}))) ⟩
        ((λ pc → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (happly (refl f)) pc) ~ happly g')
     ≃⟨ idtoeqv (ap (λ h → (λ pc → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (happly (refl f)) pc) ~ h)
                    (funext (λ x → unit-left _))) ⟩
        ((λ pc → happly f' pc ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (happly (refl f)) pc)
       ~ (λ pc → happly (refl f) (supc pc) ▪ happly g' pc)) ∎≃

-- Lemma 4.4
  Alghom≃ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} {f g : Alghom C D}
          → f ≡ g ≃ Alg~ {C = C} {D = D} f g
  Alghom≃ {C = C} {D} = AlgSec≃ {C = C} {E = (λ _ → pr₁ D) , (λ pc h → (pr₂ D) ((pr₁ pc) , h))}
  
-- Definition 4.9
  isalgequiv : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f  : Alghom C D) → Set _
  isalgequiv {C = C} {D} f = (Σ[ g ∈ (Alghom D C) ] (_∘P_ {C = C} {D = D} {E = C} g f) ≡ idAlg {C = C})
                           × (Σ[ h ∈ (Alghom D C) ] (_∘P_ {C = D} {D = C} {E = D} f h) ≡ idAlg {C = D})

  AlgEquiv : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} → Set _
  AlgEquiv {C = C} {D} = Σ[ f ∈ (Alghom C D) ] isalgequiv {C = C} {D = D} f

-- Lemma 4.11
  isalgequiv≃isequiv : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} {f : Alghom C D}
                     → isalgequiv {C = C} {D = D} f ≃ isequiv (pr₁ f)
  isalgequiv≃isequiv {C = 𝑪@(C , supc)} {𝑫@(D , supd)} {𝒇@(f , f')} =
    eq₁ ▪≃ (π , ≃→ (isContract≃isequiv π) contr) ▪≃ eq₂
    where
    open Ex2-10

    G : (g : D → C) (g' : isalghom {C = 𝑫} {D = 𝑪} g) → Set _
    G g g' = Σ[ p ∈ (g ∘ f ≡ id) ] (ap (λ z → g ∘ z) f' ▪ ap (λ z → z ∘ 𝑷 f) g' ▪ ap (λ z → supc ∘ z) (ϕ f g) ⁻¹
                                  ≡ transport (isalghom {C = 𝑪} {D = 𝑪}) (p ⁻¹) (ap (λ z → supc ∘ z) (ϕid {C = C} ⁻¹)))

    H : (h : D → C) (h' : isalghom {C = 𝑫} {D = 𝑪} h) → Set _
    H h h' = Σ[ p ∈ (f ∘ h ≡ id) ] (ap (λ z → f ∘ z) h' ▪ ap (λ z → z ∘ 𝑷 h) f' ▪ ap (λ z → supd ∘ z) (ϕ h f) ⁻¹
                                  ≡ transport (isalghom {C = 𝑫} {D = 𝑫}) (p ⁻¹) (ap (λ z → supd ∘ z) (ϕid {C = D} ⁻¹)))

    G' : (g : D → C) (p : g ∘ f ≡ id) → Set _
    G' g p = Σ[ g' ∈ isalghom {C = 𝑫} {D = 𝑪} g ] ap (λ z → g ∘ z) f' ▪ ap (λ z → z ∘ 𝑷 f) g' ▪ ap (λ z → supc ∘ z) (ϕ f g) ⁻¹
                                                 ≡ transport (isalghom {C = 𝑪} {D = 𝑪}) (p ⁻¹) (ap (λ z → supc ∘ z) (ϕid {C = C} ⁻¹))
    H' : (h : D → C) (p : f ∘ h ≡ id) → Set _
    H' h p = Σ[ h' ∈ isalghom {C = 𝑫} {D = 𝑪} h ] (ap (λ z → f ∘ z) h' ▪ ap (λ z → z ∘ 𝑷 h) f' ▪ ap (λ z → supd ∘ z) (ϕ h f) ⁻¹
                                                 ≡ transport (isalghom {C = 𝑫} {D = 𝑫}) (p ⁻¹) (ap (λ z → supd ∘ z) (ϕid {C = D} ⁻¹)))

    isContrG' : (g : D → C) (p : g ∘ f ≡ id) (qe : qinv f) → isContr (G' g p)
    isContrG' g p (f⁻¹ , ε , η) = ≃isContr (H2.isContr[[f∘q]▪p₁≡p₂] (λ z → z ∘ 𝑷 f) (qinv→isequiv qe) _ _)
                                           ((≃→Σ≃ (λ g' → r)) ⁻¹≃)
      where
      r : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
        → (p ▪ q ▪ r ≡ s) ≃ (q ▪ r ≡ p ⁻¹ ▪ s)
      r {p = refl x} {refl .x} {refl .x} {s} = idtoeqv (ap (λ t → refl x ≡ t) (unit-left s))

      qe : qinv (λ z → z ∘ 𝑷 f)
      qe = (λ z → z ∘ 𝑷 f⁻¹)
         , (λ z → ap (λ h → z ∘ h) ((ϕ f f⁻¹) ⁻¹ ▪ ap 𝑷 (funext η) ▪ ϕid))
         , (λ z → ap (λ h → z ∘ h) ((ϕ f⁻¹ f) ⁻¹ ▪ ap 𝑷 (funext ε) ▪ ϕid))

    isContrH' : (h : D → C) (p : f ∘ h ≡ id) (qe : qinv f) → isContr (H' h p)
    isContrH' h q (f⁻¹ , ε , η) = ≃isContr (H2.isContr[[f∘q]▪p₁≡p₂] (λ z → f ∘ z) (qinv→isequiv qe) _ _)
                                           ((≃→Σ≃ (λ g' → r)) ⁻¹≃)
      where
      r : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : z ≡ y} {s : w ≡ z}
        → (p ▪ q ▪ r ⁻¹ ≡ s) ≃ (p ▪ q ≡ s ▪ r)
      r {p = refl x} {refl .x} {refl .x} {s} = idtoeqv (ap (λ t → refl x ≡ t) (unit-right s))

      qe : qinv (λ z → f ∘ z)
      qe = (λ z → f⁻¹ ∘ z)
         , (λ z → ap (λ g → g ∘ z) (funext ε))
         , (λ z → ap (λ g → g ∘ z) (funext η))

    eq₁ : isalgequiv {C = 𝑪} {𝑫} 𝒇
        ≃ (Σ[ g ∈ (D → C) ] Σ[ p ∈ (g ∘ f ≡ id) ] G' g p)
        × (Σ[ h ∈ (D → C) ] Σ[ p ∈ (f ∘ h ≡ id) ] H' h p)
    eq₁ = isalgequiv {C = 𝑪} {𝑫} 𝒇
       ≃⟨ ≃→×≃ (assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ g → ≃→Σ≃ (λ g' → Σ≃ ▪≃ ≃→Σ≃ (λ p → idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p})))))
               (assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ h → ≃→Σ≃ (λ h' → Σ≃ ▪≃ ≃→Σ≃ (λ p → idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p}))))) ⟩
          (Σ[ g ∈ (D → C) ] Σ[ g' ∈ isalghom {C = 𝑫} {D = 𝑪} g ] G g g')
        × (Σ[ h ∈ (D → C) ] Σ[ h' ∈ isalghom {C = 𝑫} {D = 𝑪} h ] H h h')
       ≃⟨ ≃→×≃ (≃→Σ≃ (λ g → (λ {(g' , p , 𝑮) → p , g' , 𝑮})
                          , qinv→isequiv ( (λ {(p , g' , 𝑮) → g' , p , 𝑮})
                                         , (λ {(p , g' , 𝑮) → refl _})
                                         , (λ {(g' , p , 𝑮) → refl _}))))
               (≃→Σ≃ (λ h → (λ {(h' , p , 𝑯) → p , h' , 𝑯})
                          , qinv→isequiv ( (λ {(p , h' , 𝑯) → h' , p , 𝑯})
                                         , (λ {(p , h' , 𝑯) → refl _})
                                         , (λ {(h' , p , 𝑯) → refl _})))) ⟩
          (Σ[ g ∈ (D → C) ] Σ[ p ∈ (g ∘ f ≡ id) ] G' g p)
        × (Σ[ h ∈ (D → C) ] Σ[ p ∈ (f ∘ h ≡ id) ] H' h p) ∎≃

    eq₂ : (Σ[ g ∈ (D → C) ] (g ∘ f ≡ id))
        × (Σ[ h ∈ (D → C) ] (f ∘ h ≡ id))
        ≃ isequiv f
    eq₂ = swap×≃ ▪≃ ≃→×≃ (≃→Σ≃ (λ g → happly , funextentionality))
                         (≃→Σ≃ (λ h → happly , funextentionality))

    π : (Σ[ g ∈ (D → C) ] Σ[ p ∈ (g ∘ f ≡ id) ] G' g p)
      × (Σ[ h ∈ (D → C) ] Σ[ p ∈ (f ∘ h ≡ id) ] H' h p)
      → (Σ[ g ∈ (D → C) ] (g ∘ f ≡ id))
      × (Σ[ h ∈ (D → C) ] (f ∘ h ≡ id))
    π (𝑮 , 𝑯) = ((pr₁ 𝑮 , pr₁ (pr₂ 𝑮)) , (pr₁ 𝑯 , pr₁ (pr₂ 𝑯)))

    fib≃G'×H' : (eq : (Σ[ g ∈ (D → C) ] g ∘ f ≡ id) × (Σ[ h ∈ (D → C) ] f ∘ h ≡ id))
              → fib π eq ≃ G' (pr₁ (pr₁ eq)) (pr₂ (pr₁ eq)) × H' (pr₁ (pr₂ eq)) (pr₂ (pr₂ eq))
    fib≃G'×H' eq@((𝒈 , 𝒑) , (𝒉 , 𝒒)) = fib π eq
                                    ≃⟨ assocΣ ⁻¹≃ ▪≃ assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ g → assocΣ ⁻¹≃)
                                                  ▪≃ ≃→Σ≃ (λ g → ≃→Σ≃ (λ p → ≃→Σ≃ (λ G' → assocΣ ⁻¹≃)))
                                                  ▪≃ ≃→Σ≃ (λ g → ≃→Σ≃ (λ p → ≃→Σ≃ (λ G' → ≃→Σ≃ (λ h → assocΣ ⁻¹≃)))) ⟩
                                       Σ[ g ∈ (D → C) ] Σ[ p ∈ g ∘ f ≡ id ] Σ[ G ∈ G' g p ]
                                       Σ[ h ∈ (D → C) ] Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                       ((g , p) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                                    ≃⟨ assocΣ ▪≃ isContrA→ΣPx≃Pa _ (λ {(g , p) → Σ[ G ∈ G' g p ] Σ[ h ∈ (D → C) ]
                                                                                 Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                                                                 ((g , p) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))}) contrl ⟩
                                       Σ[ G ∈ G' 𝒈 𝒑 ] Σ[ h ∈ (D → C) ] Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                       ((𝒈 , 𝒑) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                                    ≃⟨ ≃→Σ≃ (λ G → assocΣ ▪≃ isContrA→ΣPx≃Pa _ (λ {(h , q) →
                                                               Σ[ H ∈ H' h q ] ((𝒈 , 𝒑) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))}) contrr) ⟩
                                       Σ[ G ∈ G' 𝒈 𝒑 ] Σ[ H ∈ H' 𝒉 𝒒 ]
                                       ((𝒈 , 𝒑) , (𝒉 , 𝒒)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                                    ≃⟨ ≃→Σ≃ (λ G → isContrP→ΣPx≃A _ _ (λ H → isProp→isContra (isset _ _ , refl _))) ⟩
                                       G' 𝒈 𝒑 × H' 𝒉 𝒒 ∎≃
      where
      qe : qinv f
      qe = isequiv→qinv ((𝒉 , happly 𝒒) , (𝒈 , happly 𝒑))

      contrl : isContr (Σ[ g ∈ (D → C) ] g ∘ f ≡ id)
      contrl = (𝒈 , 𝒑) , (λ {(g , p) → (pr₂ contr) _ ⁻¹ ▪ (pr₂ contr) _})
        where
        contr : isContr (Σ[ g ∈ (D → C) ] g ∘ f ≡ id)
        contr = ≃isContr (qinv→isContr[linv] f qe) linv≃Σ[g∘f≡id]

      contrr : isContr (Σ[ h ∈ (D → C) ] f ∘ h ≡ id)
      contrr = (𝒉 , 𝒒) , (λ {(h , q) → (pr₂ contr) _ ⁻¹ ▪ (pr₂ contr) _})
        where
        contr : isContr (Σ[ h ∈ (D → C) ] f ∘ h ≡ id)
        contr = ≃isContr (qinv→isContr[rinv] f qe) (rinv≃Σ[f∘g≡id] {f = f})

      isset : isSet ((Σ[ g ∈ (D → C) ] g ∘ f ≡ id) × (Σ[ h ∈ (D → C) ] f ∘ h ≡ id))
      isset = PropisSet (transport isProp (ua eq₂ ⁻¹) (biinvIsProp f))

    contr : isContract π
    contr eq@((g , p) , (h , q)) = ≃isContr (×isContr (isContrG' g p qe)
                                                      (isContrH' h q qe))
                                            (fib≃G'×H' eq ⁻¹≃)
      where
      qe = (isequiv→qinv ((h , happly q) , (g , happly p)))

-- Corollary 4.12
  isalgequivIsProp : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} {f : Alghom C D}
                   → isProp (isalgequiv {C = C} {D = D} f)
  isalgequivIsProp {C = C} {D} {f} = ≃isProp (isalgequiv≃isequiv {C = C} {D = D} ⁻¹≃) (biinvIsProp (pr₁ f))
