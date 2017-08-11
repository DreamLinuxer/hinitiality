-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-5-3 where
open import Level
open import Base
open import Ch3
open import Ch4
open import Ex2
open import hinitiality-4
open import hinitiality-5-1
open import hinitiality-5-2

data W {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) (f : B a → W A B) → W A B

indW : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'}
     → (E : W A B → Set ℓ'')
     → (e : (a : A) (f : B a → W A B) (g : (b : B a) → E (f b)) → E (sup a f))
     → (w : W A B) → E w
indW E e (sup a f) = e a f (λ b → indW E e (f b))

H-level : ∀ {ℓ} → ℕ → Set ℓ → Set _
H-level zero     A = isContr A
H-level (succ n) A = (x y : A) → H-level n (x ≡ y)

≃H-level : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ}
         → A ≃ B → H-level n A → H-level n B
≃H-level {n = zero}   eq hl = ≃isContr hl eq
≃H-level {n = succ n} (f , eq) hl x y with isequiv→qinv eq
... | (g , ε , η) = ≃H-level ((ap g , ap≡ g (qinv→isequiv (f , η , ε))) ⁻¹≃) (hl (g x) (g y))

ΠH-level : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {n : ℕ}
         → ((a : A) → H-level n (B a)) → H-level n ((a : A) → B a)
ΠH-level {n = zero}   hl = ΠisContr hl
ΠH-level {n = succ n} hl f g = ≃H-level ((happly , funextentionality) ⁻¹≃)
                                        (ΠH-level (λ a → hl a (f a) (g a)))
                                         
ΣH-level : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {n : ℕ}
         → H-level n A → ((a : A) → H-level n (B a)) → H-level n (Σ A B)
ΣH-level {n = zero}   hlA hlB = ≃isContr hlA (isContrP→ΣPx≃A _ _ hlB ⁻¹≃)
ΣH-level {n = succ n} hlA hlB (a₁ , b₁) (a₂ , b₂) = ≃H-level (Σ≃ ⁻¹≃) (ΣH-level (hlA a₁ a₂) (λ a → hlB _ _ _))
        
module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  open PAlg {A = A} {B = B}
  open Phinit {A = A} {B = B}
  open isind↔ishinit {A = A} {B = B}

-- Corollary 5.12
  supw : P (W A B) → W A B
  supw = λ {(x , u) → sup x u}

  WAlg : Alg
  WAlg = (W A B) , supw

  Wishinit : ∀ {ℓ} → ishinit {ℓ' = ℓ} WAlg
  Wishinit = isind→ishinit {C = WAlg} Wisind
    where
    Wisind : isind WAlg
    Wisind (E , e) = (indW E (λ a f → e (a , f))) , funext (λ {(x , u) → refl _})

-- Lemma 5.13
  supw≃ : (a₁ a₂ : A) (t₁ : B a₁ → W A B) (t₂ : B a₂ → W A B)
        → (supw (a₁ , t₁) ≡ supw (a₂ , t₂)) ≃ ((a₁ , t₁) ≡ (a₂ , t₂))
  supw≃ a₁ a₂ t₁ t₂ = ((ap supw) , (ap≡ supw eq)) ⁻¹≃
    where
    eq : isequiv supw
    eq = hinit→isequiv[sup] {C = WAlg} Wishinit Wishinit

-- Proposition 5.14
  W-H-level : (n : ℕ) → (H-level (succ n) A) → (H-level (succ n) (W A B))
  W-H-level n Aisn+1 w = indW (λ w → (w' : W A B) → H-level n (w ≡ w'))
                              (λ x u e → indW _ (λ x' u' _ → ≃H-level ((eq x x' u u') ⁻¹≃)
                                                                      (ΣH-level (Aisn+1 x x')
                                                                                (λ p → ΠH-level (λ b → e b (u' ((p *) b))))))) w
    where
    eq : (x x' : A) (u : B x → W A B) (u' : B x' → W A B)
       → (sup x u ≡ sup x' u') ≃ (Σ[ p ∈ (x ≡ x') ] ((y : B x) → (u y ≡ u' ((p *) y))))
    eq x x' u u' = (supw (x , u) ≡ supw (x' , u'))
                ≃⟨ supw≃ x x' u u' ⟩
                   (x , u) ≡ (x' , u')
                ≃⟨ Σ≃ ▪≃ ≃→Σ≃ (λ p → idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p})) ⟩
                   Σ[ p ∈ (x ≡ x') ] (u ≡ (p ⁻¹ *) u')
                ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ p₁ → u ≡ p₁)
                        ( transport→ {A = λ x → B x} {B = λ _ → W A B} (p ⁻¹) u'
                        ▪ funext (λ y → transportconst (W A B) (p ⁻¹) _ ▪ ap (λ q → u' ((q *) y)) (p⁻¹⁻¹≡p p))))) ⟩
                   Σ[ p ∈ (x ≡ x') ] (u ≡ (λ y → u' ((p *) y)))
                ≃⟨ ≃→Σ≃ (λ p → happly , funextentionality) ⟩
                   (Σ[ p ∈ (x ≡ x') ] ((y : B x) → (u y ≡ u' ((p *) y)))) ∎≃

-- Theorem 5.15
  uaAlg : ∀ {ℓ} {C : Alg {ℓ}} {D : Alg {ℓ}} → (C ≡ D) ≃ (AlgEquiv {C = C} {D = D})
  uaAlg {C = 𝑪@(C , supc)} {D = 𝑫@(D , supd)} =
        𝑪 ≡ 𝑫
     ≃⟨ Σ≃ ▪≃ ≃→Σ≃ (λ p → idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p})) ⟩
        Σ[ p ∈ (C ≡ D) ] (supc ≡ transport (λ C → (P C → C)) (p ⁻¹) supd)
     ≃⟨ ≃→Σ≃ (λ p → happly , funextentionality) ⟩
        Σ[ p ∈ (C ≡ D) ] ((pc : P C) → (supc pc ≡ (transport (λ C → (P C → C)) (p ⁻¹) supd) pc))
     ≃⟨ ≃→Σ≃ (λ p → ≃→Π≃ (λ {(x , u) → eq p supc supd (x , u)})) ⟩
        Σ[ p ∈ (C ≡ D) ] ((pc : P C) → (pr₁ (idtoeqv p) (supc pc) ≡ (supd ∘ 𝑷 (pr₁ (idtoeqv p))) pc))
     ≃⟨ ≃→≃Σ (idtoeqv , univalence) (λ p → ref≃) ⟩
        Σ[ eq ∈ (C ≃ D) ] ((pc : P C) → (pr₁ eq (supc pc) ≡ (supd ∘ 𝑷 (pr₁ eq)) pc))
     ≃⟨ Ex2-10.assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ f → ≃→Σ≃ (λ eq → (happly , funextentionality) ⁻¹≃)) ⟩
        Σ[ f ∈ (C → D) ] Σ[ eq ∈ (isequiv f) ] (f ∘ supc ≡ supd ∘ 𝑷 f)
     ≃⟨ (λ {(f , eq , ishom) → (f , ishom) , eq})
      , qinv→isequiv ( (λ {((f , ishom) , eq) → f , eq , ishom})
                     , (λ {((f , ishom) , eq) → refl _})
                     , (λ {(f , eq , ishom) → refl _})) ⟩
        Σ[ f ∈ (Alghom 𝑪 𝑫) ] (isequiv (pr₁ f))
     ≃⟨ ≃→Σ≃ (λ f → isalgequiv≃isequiv {C = 𝑪} {D = 𝑫} {f = f} ⁻¹≃) ⟩
        AlgEquiv ∎≃
     where
     eq : ∀ {ℓ} {C D : Set ℓ} (p : C ≡ D) (supc : P C → C) (supd : P D → D) (pc : P C)
        → (supc pc ≡ (transport (λ C → (P C → C)) (p ⁻¹) supd) pc)
        ≃ (pr₁ (idtoeqv p) (supc pc) ≡ (supd ∘ 𝑷 (pr₁ (idtoeqv p))) pc)
     eq (refl C) supc supd (x , u) = supc (x , u) ≡ supd (x , u)
                                  ≃⟨ idtoeqv (ap (λ z → supc (x , u) ≡ z)
                                             (ap (λ eq₁ → (supd ∘ 𝑷 (pr₁ eq₁)) (x , u))
                                                 (comp≡ _ ▪ ap idtoeqv ref≡ ⁻¹))) ⟩
                                     (supc (x , u)) ≡ (supd ∘ 𝑷 (pr₁ (idtoeqv (refl C)))) (x , u)
                                  ≃⟨ idtoeqv (ap (λ z → z ≡ (supd ∘ 𝑷 (pr₁ (idtoeqv (refl C)))) (x , u))
                                             (ap (λ eq → pr₁ eq (supc (x , u)))
                                                 (comp≡ _ ▪ ap idtoeqv ref≡ ⁻¹))) ⟩
                                     (pr₁ (idtoeqv (refl C)) (supc (x , u)) ≡ (supd ∘ 𝑷 (pr₁ (idtoeqv (refl C)))) (x , u)) ∎≃

-- Corollary 5.16
  hinit-uniqpath : ∀ {ℓ} (C : Alg {ℓ}) (D : Alg {ℓ})
                 → ishinit {ℓ' = ℓ} C × ishinit {ℓ' = ℓ} D → isContr (C ≡ D)
  hinit-uniqpath C D (Cishinit , Dishinit) = ≃isContr (hinit-uniqiso C D (Cishinit , Dishinit)) (uaAlg ⁻¹≃)
