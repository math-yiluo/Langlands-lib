/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible

/-!
# Transitivity of the extensions of scalars `E ⊆ E' ⊆ ℚ̄_ℓ`

Let `e : Λ → Λ'` and `e' : Λ' → ℚ̄_ℓ` be continuous `ℚ_ℓ`-algebra maps of finite extensions of
`ℚ_ℓ`. This file identifies the extension of scalars along the composite `e' ∘ e` with the
composite of the extensions of scalars
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso`):

`ℚ̄_ℓ ⊗_Λ - ≅ ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -)`,

the compatibility of the transition functors of blueprint `definition-weil-structure` with the
functors to the `ℚ̄_ℓ`-stage. It is the conjugate of the identification of the right adjoints
(`AlgebraicGeometry.ProEtale.fieldRestrictScalarsFromAdicCompIso`), restricting scalars along
`Λ_X ⟶ Λ'_X ⟶ ℚ̄_ℓ,X` in two steps or in one, which is the identity on the underlying sheaves.
Since the commutations of the extensions of scalars with the pullbacks are also conjugates of
identities, they paste compatibly
(`AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso_paste`, by
`CategoryTheory.conjugateEquiv_paste`); this is what makes the identification compatible with
the Frobenius structures of Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

section RestrictScalars

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable {R₁ R₂ R₃ : Type (u + 1)} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
  (g : R₂ →+* R₃) (X : Scheme.{u})

/-- The tensor maps of the restrictions of scalars along `f` and `g` compose to that of the
restriction of scalars along `g ∘ f`: all of them are the identity on pure tensors. -/
lemma restrictScalars_μ_comp_map_μ (M N : ModuleCat.{u + 1} R₃) :
    «μ» (ModuleCat.restrictScalars.{u + 1} f) ((ModuleCat.restrictScalars.{u + 1} g).obj M)
        ((ModuleCat.restrictScalars.{u + 1} g).obj N) ≫
      (ModuleCat.restrictScalars.{u + 1} f).map («μ» (ModuleCat.restrictScalars.{u + 1} g) M N) =
    «μ» (ModuleCat.restrictScalars.{u + 1} (g.comp f)) M N := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
  have h₁ := ModuleCat.restrictScalars_μ_tmul f ((ModuleCat.restrictScalars.{u + 1} g).obj M)
    ((ModuleCat.restrictScalars.{u + 1} g).obj N) s t
  have h₂ := ModuleCat.restrictScalars_μ_tmul g M N s t
  have h₃ := ModuleCat.restrictScalars_μ_tmul (g.comp f) M N s t
  exact (congrArg (fun x ↦ ((ModuleCat.restrictScalars.{u + 1} f).map
    («μ» (ModuleCat.restrictScalars.{u + 1} g) M N)).hom x) h₁).trans (h₂.trans h₃.symm)

/-- Restriction of scalars of sheaves along `g` and then `f` is restriction of scalars along
`g ∘ f`. -/
noncomputable def sheafComposeRestrictScalarsCompIso :
    sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} g) ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} f) ≅
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (g.comp f)) :=
  Iso.refl _

/-- The identification of the restrictions of scalars along `f ∘ g` in one or two steps is
monoidal. -/
instance isMonoidal_sheafComposeRestrictScalarsCompIso_hom :
    NatTrans.IsMonoidal (sheafComposeRestrictScalarsCompIso f g X).hom where
  unit := by
    apply Sheaf.hom_ext_of_ε_comp
    have h₁ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (g.comp f))
    have h₂ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} f)
    have h₃ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} g)
    simp only [comp_ε, sheafComposeRestrictScalarsCompIso, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp]
    rw [h₁, reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map (ε (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} g)))) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map (ε (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} g)))) from rfl, ← Functor.map_comp, h₃]
    have key : ε ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) ≫
        ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          (ε ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} g))) =
        ε ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) := by
      ext U : 2
      apply ModuleCat.hom_ext
      ext
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
      rfl
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl
  tensor P Q := by
    apply Sheaf.hom_ext_of_μ_comp
    have h₁ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (g.comp f)) P Q
    have h₂ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} f)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj P)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj Q)
    have h₃ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} g) P Q
    simp only [comp_μ, sheafComposeRestrictScalarsCompIso, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp, tensorHom_id, id_whiskerRight, Category.id_comp]
    erw [h₁]
    erw [reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map («μ» (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map («μ» (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) from rfl, ← Functor.map_comp, h₃]
    have key : «μ» ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) _ _ ≫
        ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          («μ» ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
            (ModuleCat.restrictScalars.{u + 1} g)) P.obj Q.obj) =
        «μ» ((Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) P.obj Q.obj := by
      ext U : 2
      exact restrictScalars_μ_comp_map_μ f g _ _
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl

end RestrictScalars

open scoped Obj

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  {e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l} (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (he' : Continuous e') (hc' : Continuous (algebraMap ℚ_[l] Λ'))

variable (X : Scheme.{u})

/-- Restricting scalars from `ℚ̄_ℓ` to `Λ'` and then to `Λ` is restricting scalars from `ℚ̄_ℓ`
to `Λ`, the ring maps `Λ_X ⟶ Λ'_X ⟶ ℚ̄_ℓ,X` composing to `Λ_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def fieldRestrictScalarsFromAdicCompIso :
    fieldRestrictScalarsFromAdic he' X ⋙ fieldRestrictScalars he X ≅
      fieldRestrictScalarsFromAdic (e := e'.comp e) (he'.comp he) X :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      (M := (fieldRestrictScalars he X).obj ((fieldRestrictScalarsFromAdic he' X).obj N))
      (N := (fieldRestrictScalarsFromAdic (e := e'.comp e) (he'.comp he) X).obj N) (Iso.refl _)
      (Functor.act_comp_app_of_isMonoidal
        (sheafComposeRestrictScalarsCompIso (fieldRingHom.{u} e) (fieldToAdicRingHom.{u} e') X).hom
        (fieldConstantSheafToRestrictScalars he' X) (fieldConstantSheafToRestrictScalarsField he X)
        (fieldConstantSheafToRestrictScalars (e := e'.comp e) (he'.comp he) X) rfl N))
    fun _ ↦ Mod.hom_ext _ _ rfl

/-- The extensions of scalars `ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -)` and `ℚ̄_ℓ ⊗_Λ -` agree, the conjugate of
`AlgebraicGeometry.ProEtale.fieldRestrictScalarsFromAdicCompIso`. -/
noncomputable def fieldExtendScalarsCompExtendScalarsToAdicIso :
    fieldExtendScalarsToAdic (e := e'.comp e) (he'.comp he) hc X ≅
      fieldExtendScalars he hc X ⋙ fieldExtendScalarsToAdic he' hc' X :=
  (conjugateIsoEquiv ((fieldExtendScalarsAdjunction he hc X).comp
      (fieldExtendScalarsToAdicAdjunction he' hc' X))
    (fieldExtendScalarsToAdicAdjunction (e := e'.comp e) (he'.comp he) hc X)).symm
    (fieldRestrictScalarsFromAdicCompIso he he' X)

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The commutations of the extensions of scalars with the pullback `g^*` paste: through
`ℚ̄_ℓ ⊗_Λ - ≅ ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -)`, the commutation of `ℚ̄_ℓ ⊗_Λ -` with `g^*` is the composite
of those of `Λ' ⊗_Λ -` and `ℚ̄_ℓ ⊗_{Λ'} -`. -/
lemma fieldExtendScalarsCompExtendScalarsToAdicIso_paste :
    Functor.whiskerRight (fieldExtendScalarsCompExtendScalarsToAdicIso he hc he' hc' X).hom
        (g)^*ᵃ[l] ≫
      Functor.whiskerLeft (fieldExtendScalars he hc X)
        (fieldUpperStarCompExtendScalarsToAdicIso he' hc' g).inv ≫
      Functor.whiskerRight (fieldUpperStarCompExtendScalarsIso he hc g).inv
        (fieldExtendScalarsToAdic he' hc' Y) =
    (fieldUpperStarCompExtendScalarsToAdicIso (e := e'.comp e) (he'.comp he) hc g).inv ≫
      Functor.whiskerLeft (g)^*ᶠ[Λ]
        (fieldExtendScalarsCompExtendScalarsToAdicIso he hc he' hc' Y).hom := by
  refine conjugateEquiv_paste (fieldUpperStarLowerStarAdjunction Λ g)
    (fieldUpperStarLowerStarAdjunction Λ' g) (adicUpperStarLowerStarAdjunction l g)
    (fieldExtendScalarsAdjunction he hc X) (fieldExtendScalarsAdjunction he hc Y)
    (fieldExtendScalarsToAdicAdjunction he' hc' X) (fieldExtendScalarsToAdicAdjunction he' hc' Y)
    (fieldExtendScalarsToAdicAdjunction (e := e'.comp e) (he'.comp he) hc X)
    (fieldExtendScalarsToAdicAdjunction (e := e'.comp e) (he'.comp he) hc Y) _ _ _ _ _ ?_
  simp only [fieldUpperStarCompExtendScalarsIso, fieldUpperStarCompExtendScalarsToAdicIso,
    fieldExtendScalarsCompExtendScalarsToAdicIso, conjugateIsoEquiv_symm_apply_inv,
    conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  ext
  rfl

section Field

variable {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [NormedField Λ₁] [IsUltrametricDist Λ₁] [NormedField Λ₂]
  [IsUltrametricDist Λ₂] [NormedField Λ₃] [IsUltrametricDist Λ₃] [NormedField Λ₄]
  [IsUltrametricDist Λ₄] [Algebra ℚ_[l] Λ₁] [Algebra ℚ_[l] Λ₂] [Algebra ℚ_[l] Λ₃]
  [Algebra ℚ_[l] Λ₄] [FiniteDimensional ℚ_[l] Λ₂] [FiniteDimensional ℚ_[l] Λ₃]
  [FiniteDimensional ℚ_[l] Λ₄] {e₁ : Λ₁ →ₐ[ℚ_[l]] Λ₂} {e₂ : Λ₂ →ₐ[ℚ_[l]] Λ₃}
  {e₃ : Λ₃ →ₐ[ℚ_[l]] Λ₄} (he₁ : Continuous e₁) (he₂ : Continuous e₂) (he₃ : Continuous e₃)
  (hc₁ : Continuous (algebraMap ℚ_[l] Λ₁)) (hc₂ : Continuous (algebraMap ℚ_[l] Λ₂))
  (hc₃ : Continuous (algebraMap ℚ_[l] Λ₃))

/-- Restricting scalars from `Λ₃` to `Λ₂` and then to `Λ₁` is restricting scalars from `Λ₃`
to `Λ₁`. -/
noncomputable def fieldRestrictScalarsCompIso (X : Scheme.{u}) :
    fieldRestrictScalars he₂ X ⋙ fieldRestrictScalars he₁ X ≅
      fieldRestrictScalars (e := e₂.comp e₁) (he₂.comp he₁) X :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      (M := (fieldRestrictScalars he₁ X).obj ((fieldRestrictScalars he₂ X).obj N))
      (N := (fieldRestrictScalars (e := e₂.comp e₁) (he₂.comp he₁) X).obj N) (Iso.refl _)
      (Functor.act_comp_app_of_isMonoidal
        (sheafComposeRestrictScalarsCompIso (fieldRingHom.{u} e₁) (fieldRingHom.{u} e₂) X).hom
        (fieldConstantSheafToRestrictScalarsField he₂ X)
        (fieldConstantSheafToRestrictScalarsField he₁ X)
        (fieldConstantSheafToRestrictScalarsField (e := e₂.comp e₁) (he₂.comp he₁) X) rfl N))
    fun _ ↦ Mod.hom_ext _ _ rfl

/-- The extensions of scalars `Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -)` and `Λ₃ ⊗_{Λ₁} -` agree, the conjugate
of `AlgebraicGeometry.ProEtale.fieldRestrictScalarsCompIso`. -/
noncomputable def fieldExtendScalarsCompIso (X : Scheme.{u}) :
    fieldExtendScalars (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X ≅
      fieldExtendScalars he₁ hc₁ X ⋙ fieldExtendScalars he₂ hc₂ X :=
  (conjugateIsoEquiv ((fieldExtendScalarsAdjunction he₁ hc₁ X).comp
      (fieldExtendScalarsAdjunction he₂ hc₂ X))
    (fieldExtendScalarsAdjunction (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X)).symm
    (fieldRestrictScalarsCompIso he₁ he₂ X)

/-- The commutations of the extensions of scalars with the pullback `g^*` paste through
`Λ₃ ⊗_{Λ₁} - ≅ Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -)`. -/
lemma fieldExtendScalarsCompIso_paste :
    Functor.whiskerRight (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom (g)^*ᶠ[Λ₃] ≫
      Functor.whiskerLeft (fieldExtendScalars he₁ hc₁ X)
        (fieldUpperStarCompExtendScalarsIso he₂ hc₂ g).inv ≫
      Functor.whiskerRight (fieldUpperStarCompExtendScalarsIso he₁ hc₁ g).inv
        (fieldExtendScalars he₂ hc₂ Y) =
    (fieldUpperStarCompExtendScalarsIso (e := e₂.comp e₁) (he₂.comp he₁) hc₁ g).inv ≫
      Functor.whiskerLeft (g)^*ᶠ[Λ₁] (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ Y).hom := by
  refine conjugateEquiv_paste (fieldUpperStarLowerStarAdjunction Λ₁ g)
    (fieldUpperStarLowerStarAdjunction Λ₂ g) (fieldUpperStarLowerStarAdjunction Λ₃ g)
    (fieldExtendScalarsAdjunction he₁ hc₁ X) (fieldExtendScalarsAdjunction he₁ hc₁ Y)
    (fieldExtendScalarsAdjunction he₂ hc₂ X) (fieldExtendScalarsAdjunction he₂ hc₂ Y)
    (fieldExtendScalarsAdjunction (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X)
    (fieldExtendScalarsAdjunction (e := e₂.comp e₁) (he₂.comp he₁) hc₁ Y) _ _ _ _ _ ?_
  simp only [fieldUpperStarCompExtendScalarsIso, fieldExtendScalarsCompIso,
    conjugateIsoEquiv_symm_apply_inv, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  ext
  rfl

variable (X)

omit [IsUltrametricDist Λ₁] [IsUltrametricDist Λ₂] [IsUltrametricDist Λ₃] [IsUltrametricDist Λ₄] in
/-- **The associativity constraints of the extensions of scalars satisfy the cocycle
condition**: the two identifications of `Λ₄ ⊗_{Λ₁} -` with `Λ₄ ⊗_{Λ₃} (Λ₃ ⊗_{Λ₂} (Λ₂ ⊗_{Λ₁} -))`
agree. -/
lemma fieldExtendScalarsCompIso_cocycle :
    (fieldExtendScalarsCompIso (e₁ := e₂.comp e₁) (he₂.comp he₁) he₃ hc₁ hc₃ X).hom ≫
        Functor.whiskerRight (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom
          (fieldExtendScalars he₃ hc₃ X) =
      (fieldExtendScalarsCompIso (e₂ := e₃.comp e₂) he₁ (he₃.comp he₂) hc₁ hc₂ X).hom ≫
        Functor.whiskerLeft (fieldExtendScalars he₁ hc₁ X)
          (fieldExtendScalarsCompIso he₂ he₃ hc₂ hc₃ X).hom := by
  refine conjugateEquiv_cocycle (fieldExtendScalarsAdjunction he₁ hc₁ X)
    (fieldExtendScalarsAdjunction he₂ hc₂ X) (fieldExtendScalarsAdjunction he₃ hc₃ X)
    (fieldExtendScalarsAdjunction (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X)
    (fieldExtendScalarsAdjunction (e := e₃.comp e₂) (he₃.comp he₂) hc₂ X)
    (fieldExtendScalarsAdjunction (e := e₃.comp (e₂.comp e₁)) (he₃.comp (he₂.comp he₁)) hc₁ X)
    _ _ _ _ ?_
  simp only [fieldExtendScalarsCompIso, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  ext
  rfl

omit [IsUltrametricDist Λ₁] [IsUltrametricDist Λ₂] [IsUltrametricDist Λ₃] in
/-- The cocycle condition for the associativity constraints of the extensions of scalars,
the last one being the extension of scalars to `ℚ̄_ℓ`. -/
lemma fieldExtendScalarsCompIso_cocycle_adic {e₃ : Λ₃ →ₐ[ℚ_[l]] PadicAlgCl l}
    (he₃ : Continuous e₃) [FiniteDimensional ℚ_[l] Λ₁] :
    (fieldExtendScalarsCompExtendScalarsToAdicIso (e := e₂.comp e₁) (he₂.comp he₁) hc₁ he₃ hc₃
      X).hom ≫
        Functor.whiskerRight (fieldExtendScalarsCompIso he₁ he₂ hc₁ hc₂ X).hom
          (fieldExtendScalarsToAdic he₃ hc₃ X) =
      (fieldExtendScalarsCompExtendScalarsToAdicIso (e' := e₃.comp e₂) he₁ hc₁ (he₃.comp he₂)
        hc₂ X).hom ≫
        Functor.whiskerLeft (fieldExtendScalars he₁ hc₁ X)
          (fieldExtendScalarsCompExtendScalarsToAdicIso he₂ hc₂ he₃ hc₃ X).hom := by
  refine conjugateEquiv_cocycle (fieldExtendScalarsAdjunction he₁ hc₁ X)
    (fieldExtendScalarsAdjunction he₂ hc₂ X) (fieldExtendScalarsToAdicAdjunction he₃ hc₃ X)
    (fieldExtendScalarsAdjunction (e := e₂.comp e₁) (he₂.comp he₁) hc₁ X)
    (fieldExtendScalarsToAdicAdjunction (e := e₃.comp e₂) (he₃.comp he₂) hc₂ X)
    (fieldExtendScalarsToAdicAdjunction (e := e₃.comp (e₂.comp e₁)) (he₃.comp (he₂.comp he₁))
      hc₁ X) _ _ _ _ ?_
  simp only [fieldExtendScalarsCompIso, fieldExtendScalarsCompExtendScalarsToAdicIso,
    conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  ext
  rfl

end Field

end AlgebraicGeometry.ProEtale
