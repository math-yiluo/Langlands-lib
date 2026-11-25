/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal

/-!
# The derived (Push) comparison along a quotient `𝒪_E ⟶ 𝒪_E ⧸ (ϖ)`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E`,
`a : 𝒪̲_E ⟶ Λ'` a morphism of commutative condensed rings and `ϖ ∈ 𝒪_E` a nonzero element such
that, on every scheme `X`, the sequence
```
0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ Λ'_X ⟶ 0
```
is short exact (e.g. `Λ' = 𝔽_E` with `ϖ` a uniformizer, or `Λ' = 𝒪_E ⧸ ℓⁿ` with `ϖ = ℓⁿ`).
This file generalises the residue-field results of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal` and the files it uses to
this setting:

* `ProEtale.CondensedRing.rightAcyclic_lowerStar_of_comap_of_shortExact`: a `Λ'_X`-module is
  `f_*`-acyclic as soon as its restriction of scalars to `𝒪_{E,X}` is;
* `ProEtale.CondensedRing.isIso_pushHom_app_of_rightAcyclic_of_shortExact`: the underived
  (Push) comparison `Λ'_Y ⊗ f_* M ⟶ f_*(Λ'_X ⊗ M)` is an isomorphism at every `f_*`-acyclic
  `𝒪_{E,X}`-module `M` on which `ϖ` acts injectively;
* `ProEtale.CondensedRing.exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_of_ne_zero`:
  torsion-free `f_*`-acyclic resolutions for a nonzero `ϖ`;
* `ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact`:
  **the derived (Push) comparison** `Λ' ⊗ᴸ Rf_* K ⟶ Rf_*(Λ' ⊗ᴸ K)` is an isomorphism for every
  bounded below `K ∈ D(𝒪_{E,X})`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] Bimod.monoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For `ϖ ∈ 𝒪_E` acting injectively on `𝒪_{E,X}` and `𝒪_{E,Y}`, and an injective
`𝒪_{E,X}`-module `J`, the kernel `J[ϖ]` of the action of `ϖ` on `J` is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_kernel_of_mono (ϖ : PadicAlgCl.integers ℓ E)
    [Mono (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom]
    [Mono (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ).hom]
    (J : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) [Injective J] :
    ((f)_*⟦_⟧).rightAcyclic
      (Limits.kernel (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J)) := by
  have := Mod.epi_regularEndSMul_of_injective (r := padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J
  refine Functor.rightAcyclic_kernel_of_injective _ ?_
  have h : (f)_*⟦_⟧.map (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J) =
      Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj J) :=
    Mod.hom_ext _ _ (lowerStar_map_regularEndSMul ℓ E ϖ f J)
  rw [h]
  exact Mod.epi_regularEndSMul_of_injective _

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  (a : Profinite.padicIntegersRingObj ℓ E ⟶ Λ') [IsMonHom a] (ϖ : PadicAlgCl.integers ℓ E)
  (w : ∀ X : Scheme.{u}, (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom ≫ coefficientMap a X = 0)
  (hφ : ∀ X : Scheme.{u}, (ShortComplex.mk _ _ (w X)).ShortExact)

include hφ in
/-- **The restriction of scalars to `𝒪_{E,X}` of an injective `Λ'_X`-module is `f_*`-acyclic**,
if `0 ⟶ 𝒪_E --ϖ--> 𝒪_E ⟶ Λ' ⟶ 0` is short exact on every scheme. -/
lemma rightAcyclic_lowerStar_comap_of_injective_of_shortExact
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) [Injective I] :
    ((f)_*⟦_⟧).rightAcyclic ((Mod.comap (coefficientMap a X)).obj I) := by
  have := (hφ X).mono_f
  have := (hφ Y).mono_f
  exact Mod.rightAcyclic_comap_of_injective _ (w X) (hφ X)
    (fun J _ ↦ rightAcyclic_lowerStar_kernel_of_mono ℓ E f ϖ J) I

include hφ in
/-- **`R⁺f_*` commutes with restriction of scalars along `a`**: the base change morphism
`res R⁺f_* K ⟶ R⁺f_*(res K)` is an isomorphism. -/
lemma isIso_rightDerivedFunctorPlusBaseChange_comapLowerStarIso_of_shortExact :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange (comapLowerStarIso a f).hom) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_lowerStar_comap_of_injective_of_shortExact ℓ E f a ϖ w hφ I

include hφ in
/-- **Higher direct images commute with restriction of scalars along `a`**: the base change
morphism `res R^q f_* M ⟶ R^q f_*(res M)` is an isomorphism. -/
lemma isIso_rightDerivedBaseChange_comapLowerStarIso_of_shortExact (q : ℕ) :
    IsIso (Functor.rightDerivedBaseChange (comapLowerStarIso a f).hom q) := by
  have := isIso_rightDerivedFunctorPlusBaseChange_comapLowerStarIso_of_shortExact ℓ E f a ϖ w hφ
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

include hφ in
/-- **A `Λ'_X`-module is `f_*`-acyclic as soon as its restriction of scalars to `𝒪_{E,X}`
is.** -/
theorem rightAcyclic_lowerStar_of_comap_of_shortExact
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : ((f)_*⟦_⟧).rightAcyclic ((Mod.comap (coefficientMap a X)).obj M)) :
    ((f)_*⟦Λ'⟧).rightAcyclic M := fun q ↦ by
  have := isIso_rightDerivedBaseChange_comapLowerStarIso_of_shortExact ℓ E f a ϖ w hφ (q + 1)
  have hz : IsZero ((Mod.comap (coefficientMap a Y)).obj
      ((((f)_*⟦_⟧).rightDerived (q + 1)).obj M)) :=
    (hM q).of_iso ((asIso (Functor.rightDerivedBaseChange
      (comapLowerStarIso a f).hom (q + 1))).app M)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact (Mod.comap _).map_injective (by rw [CategoryTheory.Functor.map_id, Functor.map_zero, hz])

include hφ in
/-- **The underived (Push) comparison along `a`** is an isomorphism at an `𝒪_{E,X}`-module `M`
on which `ϖ` acts injectively and whose underlying abelian sheaf is `f_*`-acyclic: both units
`f_* M ⟶ Λ'_Y ⊗ f_* M` and `f_* M ⟶ f_*(Λ'_X ⊗ M)` are cokernels of the action of `ϖ` on
`f_* M`, the second one since `R¹f_* M = 0`. -/
theorem isIso_pushHom_app_of_mono_of_shortExact
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    [Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)]
    (hM : ((f)_*[Ab.{u + 1}]).rightAcyclic M.X) :
    IsIso ((pushHom a f).app M) := by
  have hX := Mod.shortExact_regularEndSMul_extendUnit (w X) (hφ X) M
  have := hX.mono_f
  have := hX.epi_g
  have : Mono ((Mod.forget _).map
      (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)) :=
    (Mod.forget _).map_mono _
  have : Epi ((Mod.forget _).map (Mod.extendUnit (coefficientMap a X) M)) :=
    (Mod.forget _).map_epi _
  have hX' := (hX.map (Mod.forget _)).map_of_rightAcyclic (F := (f)_*[Ab.{u + 1}]) hM
  obtain ⟨hY, _⟩ := Mod.exact_regularEndSMul_extendUnit (w Y) (hφ Y) ((f)_*⟦_⟧.obj M)
  have hY' := hY.map (Mod.forget _)
  have : Epi ((ShortComplex.mk _ _ (Mod.regularEndSMul_comp_extendUnit (w Y)
      ((f)_*⟦_⟧.obj M))).map (Mod.forget _)).g :=
    (Mod.forget _).map_epi _
  have e := lowerStar_map_regularEndSMul ℓ E ϖ f M
  have w₂ : (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj M)).hom ≫
      (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a X) M) = 0 := by
    rw [← e, ← Functor.map_comp, ← Mod.extendUnit_hom, ← Mod.comp_hom',
      Mod.regularEndSMul_comp_extendUnit (w X), Mod.zero_hom, Functor.map_zero]
  have hX'' : (ShortComplex.mk _ _ w₂).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk
      (S₁ := ((ShortComplex.mk _ _ (Mod.regularEndSMul_comp_extendUnit (w X) M)).map
        (Mod.forget _)).map (f)_*[Ab.{u + 1}]) (S₂ := ShortComplex.mk _ _ w₂) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simpa using e.symm) (by simp)) hX'.exact
  have : Epi (ShortComplex.mk _ _ w₂).g := hX'.epi_g
  exact isIso_pushHom_app_of_isColimit _ f M _ _ w₂ hY'.gIsCokernel hX''.gIsCokernel

include hφ in
/-- **The underived (Push) comparison along `a`** is an isomorphism at an `f_*`-acyclic
`𝒪_{E,X}`-module `M` on which `ϖ` acts injectively. -/
theorem isIso_pushHom_app_of_rightAcyclic_of_shortExact
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    [Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)]
    (hM : ((f)_*⟦_⟧).rightAcyclic M) :
    IsIso ((pushHom a f).app M) :=
  isIso_pushHom_app_of_mono_of_shortExact ℓ E f a ϖ w hφ M
    (rightAcyclic_forget_of_rightAcyclic_lowerStar _ f hM)

/-- **Torsion-free `f_*`-acyclic resolutions for `𝒪_E`-coefficients**: for `ϖ ∈ 𝒪_E` nonzero,
every bounded below `K ≥ n` in `D(𝒪_{E,X})` is represented by a complex `J ≥ n - 1` of
`f_*`-acyclic `𝒪_{E,X}`-modules on which `ϖ` acts injectively. -/
theorem exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_of_ne_zero (hϖ : (ϖ : E) ≠ 0)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    ∃ (J : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ℤ),
      Nonempty (K ≅ DerivedCategory.Q.obj J) ∧ J.IsStrictlyGE (n - 1) ∧
      (∀ k, Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) (J.X k))) ∧
      ∀ k, ((f)_*⟦_⟧).rightAcyclic (J.X k) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let ιY := Mod.regularToComapRegular (padicIntegersToSubfieldRingObj Y ℓ E)
  have : Mono ιY := Mod.mono_regularToComapRegular _
  let ιX := Functor.LaxMonoidal.ε (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧ ≫
    (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.map ιY
  have : Mono ιX := mono_comp _ _
  let e := upperStarComapPadicSubfieldIso ℓ E f
  have : Functor.PreservesMonomorphisms (tensorLeft ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj
      ((Mod.comap (padicIntegersToSubfieldRingObj Y ℓ E)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) Y))))) := by
    have := Mod.preservesMonomorphisms_tensorLeft_comap_regular
      (padicIntegersToSubfieldRingObj X ℓ E)
    exact Functor.PreservesMonomorphisms.of_iso ((tensoringLeft _).mapIso e.symm)
  have : Epi (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)
      ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj
        ((Mod.comap (padicIntegersToSubfieldRingObj Y ℓ E)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) Y))))) := by
    have := epi_regularEndSMul_comap_padicSubfield X ℓ E ϖ hϖ
    have h := Mod.regularEndSMul_naturality (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) e.hom
    rw [show Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) _ = _ ≫ _ ≫ e.inv from
      (by rw [← reassoc_of% h, e.hom_inv_id, Category.comp_id])]
    infer_instance
  obtain ⟨J, hK, hJ, hr, hG⟩ := exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic _ ιX
    (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) K n
  exact ⟨J, hK, hJ, hr, fun k ↦ hG f ιY (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id]) k⟩

include hφ in
/-- **The derived (Push) comparison along `𝒪_E ⟶ 𝒪_E ⧸ (ϖ)`**: if `ϖ ∈ 𝒪_E` is nonzero and
`0 ⟶ 𝒪_E --ϖ--> 𝒪_E ⟶ Λ' ⟶ 0` is short exact on every scheme, then for every morphism of
schemes `f : X ⟶ Y` and every bounded below `K ∈ D(𝒪_{E,X})`, the comparison
`Λ' ⊗ᴸ Rf_* K ⟶ Rf_*(Λ' ⊗ᴸ K)` is an isomorphism. -/
theorem isIso_derivedUpperStarExtendScalarsPushHom_app_of_shortExact (hϖ : (ϖ : E) ≠ 0)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedUpperStarExtendScalarsPushHom a f).app K) := by
  have hJ := exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_of_ne_zero ℓ E f ϖ hϖ K n
  obtain ⟨J, ⟨e⟩, hJn, hr, hJ⟩ := hJ
  have := (hφ X).mono_f
  have := (hφ Y).mono_f
  have hY : ∀ k, Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ)
      ((f)_*⟦_⟧.obj (J.X k))) := fun k ↦ by
    have := hr k
    have h : (f)_*⟦_⟧.map (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) (J.X k)) =
        Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj (J.X k)) :=
      Mod.hom_ext _ _ (lowerStar_map_regularEndSMul ℓ E ϖ f (J.X k))
    rw [← h]
    infer_instance
  -- The conclusion differs from the goal only in proof arguments; at default transparency the
  -- unifier unfolds the morphisms of the derived categories instead (minutes).
  with_reducible
    refine isIso_derivedUpperStarExtendScalarsPushHom_app_of_isStrictlyGE _ f K J e (n - 1) hJ
      (fun k ↦ ?_) (fun k ↦ ?_) ?_ ?_
  · have := hr k
    exact rightAcyclic_lowerStar_of_comap_of_shortExact ℓ E f a ϖ w hφ _
      ((Mod.shortExact_regularEndSMul_extendUnit (w X) (hφ X) (J.X k)).rightAcyclic_X₃
        (hJ k) (hJ k))
  · have := hr k
    exact isIso_pushHom_app_of_rightAcyclic_of_shortExact ℓ E f a ϖ w hφ (J.X k) (hJ k)
  · exact Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul (w X) (hφ X) J hr
  · exact Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul (w Y) (hφ Y)
      ((((f)_*⟦_⟧).mapHomologicalComplex _).obj J) hY

end AlgebraicGeometry.ProEtale.CondensedRing
