-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-2 where
open import Level
open import Base
open import Ch3
open import Ch4
open import Ex2

Bip : ∀ {ℓ} → Set _
Bip {ℓ} = Σ[ A ∈ Set ℓ ] (A × A)

Bipmorphism : ∀ {ℓ ℓ'} → (A : Bip {ℓ}) (B : Bip {ℓ'}) → Set _
Bipmorphism A B = Σ[ f ∈ (pr₁ A → pr₁ B) ] ((f (pr₁ (pr₂ A)) ≡ (pr₁ (pr₂ B))) × (f (pr₂ (pr₂ A)) ≡ (pr₂ (pr₂ B))))

_∘b_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Bip {ℓ₁}} {B : Bip {ℓ₂}} {C : Bip {ℓ₃}}
     → Bipmorphism B C → Bipmorphism A B → Bipmorphism A C
_∘b_ (g , g₀ , g₁) (f , f₀ , f₁) = (g ∘ f) , (ap g f₀ ▪ g₀ , ap g f₁ ▪ g₁)

idBip : ∀ {ℓ} {A : Bip {ℓ}} → Bipmorphism A A
idBip = id , (refl _ , refl _)

Bip~ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {B : Bip {ℓ'}} → Bipmorphism A B → Bipmorphism A B → Set _
Bip~ (f , f₀ , f₁) (g , g₀ , g₁) = Σ[ α ∈ (f ~ g) ] ((f₀ ≡ α _ ▪ g₀) × (f₁ ≡ α _ ▪ g₁))

-- Lemma 2.4
Bip≃ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {B : Bip {ℓ'}} (f g : Bipmorphism A B)
     → (f ≡ g) ≃ (Bip~ {A = A} {B} f g)

-- Definition 2.5
FibBip : ∀ {ℓ ℓ'} (A : Bip {ℓ}) → Set (suc ℓ' ⊔ ℓ)
FibBip {ℓ' = ℓ'} A = Σ[ E ∈ (pr₁ A → Set ℓ') ] (E (pr₁ (pr₂ A)) × E (pr₂ (pr₂ A)))

-- Definition 2.6
BipSec : ∀ {ℓ ℓ'} (A : Bip {ℓ}) (E : FibBip {ℓ' = ℓ'} A) → Set (ℓ' ⊔ ℓ)
BipSec (A , a₀ , a₁) (E , e₀ , e₁) = Σ[ f ∈ ((x : A) → E x) ] ((f a₀ ≡ e₀) × (f a₁ ≡ e₁))

-- Definition 2.7
BipSec~ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {E : FibBip {ℓ' = ℓ'} A}
        → (f g : BipSec A E) → Set (ℓ' ⊔ ℓ)
BipSec~ {A = (A , a₀ , a₁)} {E = (E , e₀ , e₁)} (f , f₀ , f₁) (g , g₀ , g₁)
      = Σ[ α ∈ (f ~ g) ] ((f₀ ≡ α a₀ ▪ g₀) × (f₁ ≡ α a₁ ▪ g₁))

-- Lemma 2.8
BipSec≃ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {E : FibBip {ℓ' = ℓ'} A}
        → (f g : BipSec A E) → (f ≡ g) ≃ (BipSec~ f g)
BipSec≃ {A = (A , a₀ , a₁)} {E = (E , e₀ , e₁)} (f , f₀ , f₁) (g , g₀ , g₁) =
     (f , f₀ , f₁) ≡ (g , g₀ , g₁)
  ≃⟨ Σ≃ ⟩
     Σ[ p ∈ (f ≡ g) ] (p *) (f₀ , f₁) ≡ (g₀ , g₁)
  ≃⟨ ≃→Σ≃ (λ p → (eq₁ p) ▪≃ (pair×≡⁻¹ , ×≃)) ⟩
     Σ[ p ∈ (f ≡ g) ] (((p *) f₀ ≡ g₀) × ((p *) f₁ ≡ g₁))
  ≃⟨ ≃→Σ≃ (λ p → ≃→×≃ (eq₂ p _ _ f₀ g₀) (eq₂ p _ _ f₁ g₁)) ⟩
     Σ[ p ∈ (f ≡ g) ] ((f₀ ≡ (p ⁻¹ *) g₀) × (f₁ ≡ (p ⁻¹ *) g₁))
  ≃⟨ ≃→Σ≃ (λ p → ≃→×≃ (eq₃ p _ _ f₀ g₀) (eq₃ p _ _ f₁ g₁)) ⟩
     Σ[ p ∈ (f ≡ g) ] ((f₀ ≡ (happly p) _ ▪ g₀) × (f₁ ≡ (happly p) _ ▪ g₁))
  ≃⟨ ≃→≃Σ (happly , funextentionality) (λ a → ≃→×≃ ref≃ ref≃) ⟩
     BipSec~ {A = (A , a₀ , a₁)} {E = (E , e₀ , e₁)} (f , f₀ , f₁) (g , g₀ , g₁) ∎≃
  where
  eq₁ : (p : f ≡ g) → ((p *) (f₀ , f₁) ≡ g₀ , g₁) ≃ (((p *) f₀ , (p *) f₁) ≡ g₀ , g₁)
  eq₁ (refl _) = idtoeqv (refl _)

  eq₂ : (p : f ≡ g) (a : A) (b : E a) (f' : f a ≡ b) (g' : g a ≡ b)
      → ((p *) f' ≡ g') ≃ (f' ≡ ((p ⁻¹) *) g')
  eq₂ (refl _) a _ (refl _) g' = idtoeqv (refl _)

  eq₃ : (p : f ≡ g) (a : A) (b : E a) (f' : f a ≡ b) (g' : g a ≡ b)
      → f' ≡ ((p ⁻¹) *) g' ≃ f' ≡ happly p a ▪ g'
  eq₃ (refl _) a _ (refl _) g' = idtoeqv (ap (λ q → refl (f a) ≡ q) (unit-left g'))

Bip≃ {A = (A , a₀ , a₁)} {B = (B , b₀ , b₁)} (f , f₀ , f₁) (g , g₀ , g₁) =
     BipSec≃ {A = A , a₀ , a₁} {E = (λ a → B) , b₀ , b₁} (f , f₀ , f₁) (g , g₀ , g₁)

isbipequiv : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {B : Bip {ℓ'}} (f : Bipmorphism A B) → Set _
isbipequiv {A = A} {B} f = (Σ[ g ∈ (Bipmorphism B A) ] (_∘b_ {A = A} {B = B} {C = A} g f ≡ id , (refl _ , refl _)))
                         × (Σ[ h ∈ (Bipmorphism B A) ] (_∘b_ {A = B} {B = A} {C = B} f h ≡ id , (refl _ , refl _)))

BipEquiv : ∀ {ℓ ℓ'} (A : Bip {ℓ}) (B : Bip {ℓ'}) → Set _
BipEquiv A B = Σ[ f ∈ (Bipmorphism A B) ] (isbipequiv {A = A} {B} f)

-- Lemma 2.11
isContr[Σp₁▪q≡p₂] : ∀ {ℓ} {A : Set ℓ} {a a₁ a₂ : A} (p₁ : a ≡ a₁) (p₂ : a ≡ a₂)
                  → isContr (Σ[ q ∈ (a₁ ≡ a₂) ] (p₁ ▪ q) ≡ p₂)
isContr[Σp₁▪q≡p₂] (refl x) (refl .x) = ≃isContr (Σ[x≡a]isContr (x ≡ x) (refl _)) (≃→Σ≃ eq)
  where
  eq : (q : x ≡ x) → q ≡ refl x ≃ refl x ▪ q ≡ refl x
  eq q = idtoeqv (ap (λ p → p ≡ refl x) (unit-left q))

isContr[[f∘q]▪p₁≡p₂] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} {b : B} (f : A → B) → isequiv f
                     → (p₁ : f a₁ ≡ b) (p₂ : f a₂ ≡ b)
                     → isContr (Σ[ q ∈ (a₂ ≡ a₁) ] (ap f q ▪ p₁ ≡ p₂))
isContr[[f∘q]▪p₁≡p₂] {a₁ = a₁} {a₂} {b} f feq p₁ p₂ with hae→isContr[fib] (≃→ (biinv≃ishae f) feq) b
... | (fi , contr) = ≃isContr isContr[fi≡fi] eq
  where
  isContr[fi≡fi] : isContr ((a₂ , p₂) ≡ (a₁ , p₁))
  isContr[fi≡fi] = (contr (a₂ , p₂) ⁻¹ ▪ contr (a₁ , p₁)
                 ,  PropisSet (pr₁ (isContra→isProp (fi , contr))) _ _ _)

  eq : a₂ , p₂ ≡ a₁ , p₁ ≃ (Σ[ q ∈ (a₂ ≡ a₁)] (ap f q ▪ p₁ ≡ p₂))
  eq = [x,p≡x,p']≃Σ[fγ▪p'≡p] f b (a₂ , p₂) (a₁ , p₁)

-- Proposition 2.12
isbipequiv≃isequiv : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {B : Bip {ℓ'}} {f : Bipmorphism A B}
                   → isbipequiv {A = A} {B} f ≃ isequiv (pr₁ f)
isbipequiv≃isequiv {ℓ} {ℓ'} {A = 𝑨@(A , a₀ , a₁)} {B = 𝑩@(B , b₀ , b₁)} {f = 𝒇@(f , f₀ , f₁)} =
  eq₁ ▪≃ (π , ≃→ (isContract≃isequiv π) contr) ▪≃ eq₂
  where
  open Ex2-10
  P : ∀ {ℓ} {A : Set ℓ} → A → (A → A) → Set _
  P a f = f a ≡ a

  G' : (g : B → A) (p : g ∘ f ≡ id) → Set _
  G' g p = (Σ[ g₀ ∈ g b₀ ≡ a₀ ] ap g f₀ ▪ g₀ ≡ transport (P a₀) (p ⁻¹) (refl a₀))
         × (Σ[ g₁ ∈ g b₁ ≡ a₁ ] ap g f₁ ▪ g₁ ≡ transport (P a₁) (p ⁻¹) (refl a₁))

  H' : (h : B → A) (q : f ∘ h ≡ id) → Set _
  H' h q = (Σ[ h₀ ∈ h b₀ ≡ a₀ ] ap f h₀ ▪ f₀ ≡ transport (P b₀) (q ⁻¹) (refl b₀))
         × (Σ[ h₁ ∈ h b₁ ≡ a₁ ] ap f h₁ ▪ f₁ ≡ transport (P b₁) (q ⁻¹) (refl b₁))

  eq₁ : isbipequiv {A = (A , a₀ , a₁)} {B = B , b₀ , b₁} (f , f₀ , f₁)
      ≃ (Σ[ g ∈ (B → A) ] Σ[ p ∈ g ∘ f ≡ id ] G' g p) × (Σ[ h ∈ (B → A) ] Σ[ q ∈ f ∘ h ≡ id ] H' h q)
  eq₁ = (Σ[ 𝒈 ∈ (Bipmorphism 𝑩 𝑨) ] (_∘b_ {A = 𝑨} {B = 𝑩} {C = 𝑨} 𝒈 𝒇 ≡ id , (refl _ , refl _)))
      × (Σ[ 𝒉 ∈ (Bipmorphism 𝑩 𝑨) ] (_∘b_ {A = 𝑩} {B = 𝑨} {C = 𝑩} 𝒇 𝒉 ≡ id , (refl _ , refl _)))
     ≃⟨ ≃→×≃ (assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ g → assocΣ ⁻¹≃))
             (assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ h → assocΣ ⁻¹≃)) ⟩
        (Σ[ g ∈ (B → A) ] Σ[ g₀ ∈ (g b₀ ≡ a₀) ] Σ[ g₁ ∈ (g b₁ ≡ a₁) ] (g ∘ f) , (ap g f₀ ▪ g₀ , ap g f₁ ▪ g₁) ≡ id , (refl _ , refl _) )
      × (Σ[ h ∈ (B → A) ] Σ[ h₀ ∈ (h b₀ ≡ a₀) ] Σ[ h₁ ∈ (h b₁ ≡ a₁) ] (f ∘ h) , (ap f h₀ ▪ f₀ , ap f h₁ ▪ f₁) ≡ id , (refl _ , refl _) )
     ≃⟨ ≃→×≃ (≃→Σ≃ (λ g → ≃→Σ≃ (λ g₀ → ≃→Σ≃ (λ g₁ → Σ≃))))
             (≃→Σ≃ (λ h → ≃→Σ≃ (λ h₀ → ≃→Σ≃ (λ h₁ → Σ≃)))) ⟩
        (Σ[ g ∈ (B → A) ] Σ[ g₀ ∈ (g b₀ ≡ a₀) ] Σ[ g₁ ∈ (g b₁ ≡ a₁) ] Σ[ p ∈ (g ∘ f) ≡ id ]
         transport (λ g → (g a₀ ≡ a₀) × (g a₁ ≡ a₁)) p (ap g f₀ ▪ g₀ , ap g f₁ ▪ g₁) ≡ (refl _ , refl _))
      × (Σ[ h ∈ (B → A) ] Σ[ h₀ ∈ (h b₀ ≡ a₀) ] Σ[ h₁ ∈ (h b₁ ≡ a₁) ] Σ[ q ∈ (f ∘ h) ≡ id ]
         transport (λ h → (h b₀ ≡ b₀) × (h b₁ ≡ b₁)) q (ap f h₀ ▪ f₀ , ap f h₁ ▪ f₁) ≡ (refl _ , refl _) )
     ≃⟨ ≃→×≃ (≃→Σ≃ (λ g → ≃→Σ≃ (λ g₀ → ≃→Σ≃ (λ g₁ → ≃→Σ≃ (λ p → idtoeqv (ap (λ x → x ≡ refl (id a₀) , refl (id a₁)) (transport× p _))
                                                             ▪≃ (pair×≡⁻¹ , ×≃)
                                                             ▪≃ ≃→×≃ (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p}))
                                                                     (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p})))))))
             (≃→Σ≃ (λ h → ≃→Σ≃ (λ h₀ → ≃→Σ≃ (λ h₁ → ≃→Σ≃ (λ q → idtoeqv (ap (λ x → x ≡ refl (id b₀) , refl (id b₁)) (transport× q _))
                                                             ▪≃ (pair×≡⁻¹ , ×≃)
                                                             ▪≃ ≃→×≃ (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = q}))
                                                                     (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = q}))))))) ⟩
        (Σ[ g ∈ (B → A) ] Σ[ g₀ ∈ (g b₀ ≡ a₀) ] Σ[ g₁ ∈ (g b₁ ≡ a₁) ] Σ[ p ∈ (g ∘ f) ≡ id ]
         (ap g f₀ ▪ g₀ ≡ transport (P a₀) (p ⁻¹) (refl a₀)) × (ap g f₁ ▪ g₁ ≡ transport (P a₁) (p ⁻¹) (refl a₁)))
      × (Σ[ h ∈ (B → A) ] Σ[ h₀ ∈ (h b₀ ≡ a₀) ] Σ[ h₁ ∈ (h b₁ ≡ a₁) ] Σ[ q ∈ (f ∘ h) ≡ id ]
         ((ap f h₀ ▪ f₀ ≡ transport (P b₀) (q ⁻¹) (refl b₀)) × (ap f h₁ ▪ f₁ ≡ transport (P b₁) (q ⁻¹) (refl b₁))))
     ≃⟨ ≃→×≃ ( (λ {(g , g₀ , g₁ , p , p₀ , p₁) → g , p , (g₀ , p₀) , (g₁ , p₁)})
             , qinv→isequiv ( (λ {(g , p , (g₀ , g₁)) → g , pr₁ g₀ , pr₁ g₁ , p , pr₂ g₀ , pr₂ g₁})
                            , (λ {(g , p , (g₀ , p₀) , (g₁ , p₁)) → refl _})
                            , (λ {(g , g₀ , g₁ , p , p₀ , p₁) → refl _})))
             ( (λ {(h , h₀ , h₁ , p , p₀ , p₁) → h , p , (h₀ , p₀) , (h₁ , p₁)})
             , qinv→isequiv ( (λ {(h , p , (h₀ , h₁)) → h , pr₁ h₀ , pr₁ h₁ , p , pr₂ h₀ , pr₂ h₁})
                            , (λ {(h , p , (h₀ , p₀) , (h₁ , p₁)) → refl _})
                            , (λ {(h , h₀ , h₁ , p , p₀ , p₁) → refl _}))) ⟩
        (Σ[ g ∈ (B → A) ] Σ[ p ∈ g ∘ f ≡ id ] G' g p) × (Σ[ h ∈ (B → A) ] Σ[ q ∈ f ∘ h ≡ id ] H' h q) ∎≃

  eq₂ : (Σ[ g ∈ (B → A) ] g ∘ f ≡ id) × (Σ[ h ∈ (B → A) ] f ∘ h ≡ id) ≃ isequiv f
  eq₂ = swap×≃ ▪≃ ≃→×≃ (≃→Σ≃ (λ g → happly , funextentionality))
                       (≃→Σ≃ (λ h → happly , funextentionality))

  π : (Σ[ g ∈ (B → A) ] Σ[ p ∈ g ∘ f ≡ id ] G' g p) × (Σ[ h ∈ (B → A) ] Σ[ q ∈ f ∘ h ≡ id ] H' h q)
    → (Σ[ g ∈ (B → A) ] g ∘ f ≡ id) × (Σ[ h ∈ (B → A) ] f ∘ h ≡ id)
  π (G , H) = ((pr₁ G , pr₁ (pr₂ G)) , (pr₁ H , pr₁ (pr₂ H)))

  fib≃G'×H' : (eq : (Σ[ g ∈ (B → A) ] g ∘ f ≡ id) × (Σ[ h ∈ (B → A) ] f ∘ h ≡ id))
            → fib π eq ≃ G' (pr₁ (pr₁ eq)) (pr₂ (pr₁ eq)) × H' (pr₁ (pr₂ eq)) (pr₂ (pr₂ eq))
  fib≃G'×H' ((𝒈 , 𝒑) , (𝒉 , 𝒒)) = fib π ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                               ≃⟨ assocΣ ⁻¹≃ ▪≃ assocΣ ⁻¹≃ ▪≃ ≃→Σ≃ (λ g → assocΣ ⁻¹≃)
                                             ▪≃ ≃→Σ≃ (λ g → ≃→Σ≃ (λ p → ≃→Σ≃ (λ G' → assocΣ ⁻¹≃)))
                                             ▪≃ ≃→Σ≃ (λ g → ≃→Σ≃ (λ p → ≃→Σ≃ (λ G' → ≃→Σ≃ (λ h → assocΣ ⁻¹≃)))) ⟩
                                  Σ[ g ∈ (B → A) ] Σ[ p ∈ g ∘ f ≡ id ] Σ[ G ∈ G' g p ]
                                  Σ[ h ∈ (B → A) ] Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                  ((g , p) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                               ≃⟨ assocΣ ▪≃ isContrA→ΣPx≃Pa _ (λ {(g , p) → Σ[ G ∈ G' g p ] Σ[ h ∈ (B → A) ]
                                                                            Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                                                            ((g , p) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))}) contrl ⟩
                                  Σ[ G ∈ G' 𝒈 𝒑 ] Σ[ h ∈ (B → A) ] Σ[ q ∈ f ∘ h ≡ id ] Σ[ H ∈ H' h q ]
                                  ((𝒈 , 𝒑) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                               ≃⟨ ≃→Σ≃ (λ G → assocΣ ▪≃ isContrA→ΣPx≃Pa _ (λ {(h , q) →
                                                          Σ[ H ∈ H' h q ] ((𝒈 , 𝒑) , (h , q)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))}) contrr) ⟩
                                  Σ[ G ∈ G' 𝒈 𝒑 ] Σ[ H ∈ H' 𝒉 𝒒 ]
                                  ((𝒈 , 𝒑) , (𝒉 , 𝒒)) ≡ ((𝒈 , 𝒑) , (𝒉 , 𝒒))
                               ≃⟨ ≃→Σ≃ (λ G → isContrP→ΣPx≃A _ _ (λ H → isProp→isContra (isset _ _ , refl _))) ⟩
                                  (G' 𝒈 𝒑 × H' 𝒉 𝒒) ∎≃
    where
    qe : qinv f
    qe = isequiv→qinv ((𝒉 , happly 𝒒) , (𝒈 , happly 𝒑))

    contrl : isContr (Σ[ g ∈ (B → A) ] g ∘ f ≡ id)
    contrl = (𝒈 , 𝒑) , (λ {(g , p) → (pr₂ contr) _ ⁻¹ ▪ (pr₂ contr) _})
      where
      contr : isContr (Σ[ g ∈ (B → A) ] g ∘ f ≡ id)
      contr = ≃isContr (qinv→isContr[linv] f qe) linv≃Σ[g∘f≡id]

    contrr : isContr (Σ[ h ∈ (B → A) ] f ∘ h ≡ id)
    contrr = (𝒉 , 𝒒) , (λ {(h , q) → (pr₂ contr) _ ⁻¹ ▪ (pr₂ contr) _})
      where
      contr : isContr (Σ[ h ∈ (B → A) ] f ∘ h ≡ id)
      contr = ≃isContr (qinv→isContr[rinv] f qe) (rinv≃Σ[f∘g≡id] {f = f})

    isset : isSet ((Σ[ g ∈ (B → A) ] g ∘ f ≡ id) × (Σ[ h ∈ (B → A) ] f ∘ h ≡ id))
    isset = PropisSet (transport isProp (ua eq₂ ⁻¹) (biinvIsProp f))

  contr : isContract π
  contr eq = ≃isContr (×isContr (×isContr (isContr[Σp₁▪q≡p₂] _ _) (isContr[Σp₁▪q≡p₂] _ _))
                                (×isContr (isContr[[f∘q]▪p₁≡p₂] f ((≃→ eq₂) eq) _ _)
                                          (isContr[[f∘q]▪p₁≡p₂] f ((≃→ eq₂) eq) _ _)))
                      ((fib≃G'×H' eq) ⁻¹≃)

-- Corollary 2.13
isbipequivIsProp : ∀ {ℓ ℓ'} {A : Bip {ℓ}} {B : Bip {ℓ'}} {f : Bipmorphism A B}
                 → isProp (isbipequiv {A = A} {B = B} f)
isbipequivIsProp = transport isProp (ua isbipequiv≃isequiv ⁻¹) (biinvIsProp _)
