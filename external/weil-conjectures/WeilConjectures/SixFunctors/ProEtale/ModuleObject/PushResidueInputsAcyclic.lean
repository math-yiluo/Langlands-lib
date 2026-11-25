/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedPlus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueInputs

/-!
# Restrictions of scalars of injective modules along `R ⟶ R ⧸ r`

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions, `φ : R ⟶ S` a morphism of commutative algebra objects and `r` an endomorphism of the
regular `R`-module such that `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact. We show:

* `CategoryTheory.Mod.epi_regularEndSMul_of_injective`: `r` acts surjectively on injective
  `R`-modules (injective modules are divisible), since it acts injectively on flat modules;
* `CategoryTheory.Mod.regularEndSMul_comap_eq_zero`: `r` acts by zero on restrictions of scalars
  of `S`-modules, and conversely an `R`-module killed by `r` is the restriction of scalars of its
  reduction (`CategoryTheory.Mod.isIso_extendUnit_of_regularEndSMul_eq_zero`);
* `CategoryTheory.Mod.rightAcyclic_comap_of_injective`: for an additive functor `F` on
  `R`-modules such that the kernels `J[r]` of `r` on injective `R`-modules `J` are `F`-acyclic, the
  restriction of scalars of every injective `S`-module `I` is `F`-acyclic: it is a direct summand
  of `J[r]` for an injective envelope `J` of the restriction of scalars of `I`.

Applied to `𝒪_{E,X} ⟶ 𝔽_{E,X}` and the pushforward along a morphism of schemes `f`, the kernels
`J[ϖ]` are `f_*`-acyclic (`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_lowerStar_kernel`),
so that the higher direct images of `𝔽_{E,X}`-modules can be computed after restriction of
scalars to `𝒪_{E,X}` (`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_lowerStar_of_comap`).

Finally, since `𝒪_{E,X}` is flat, `f_*`-acyclicity of an `𝒪_{E,X}`-module implies that of its
underlying abelian sheaf
(`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_forget_of_rightAcyclic_lowerStar`), so
the underived (Push) comparison for `𝒪_E ⟶ 𝔽_E` is invertible at every `f_*`-acyclic module on
which `ϖ` acts injectively
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_pushHom_residueField_app_of_rightAcyclic`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory

/-- If `g : J ⟶ J'` is an epimorphism between injective objects such that `F g` is an
epimorphism, then the kernel of `g` is `F`-acyclic. -/
lemma Functor.rightAcyclic_kernel_of_injective {A D : Type*} [Category* A] [Category* D]
    [Abelian A] [HasInjectiveResolutions A] [Abelian D] {F : A ⥤ D} [F.Additive]
    [PreservesFiniteLimits F] {J J' : A} [Injective J] [Injective J'] (g : J ⟶ J') [Epi g]
    (hg : Epi (F.map g)) : F.rightAcyclic (Limits.kernel g) := by
  have hS : (ShortComplex.mk (Limits.kernel.ι g) g (Limits.kernel.condition g)).ShortExact :=
    { exact := ShortComplex.exact_kernel g }
  intro q
  obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hS.exists_rightDerived_δ_exact F q
  have hepi : Epi ((F.rightDerived q).map g) := by
    rcases q with _ | q
    · rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf g]
      infer_instance
    · exact ((F.rightAcyclic_of_injective J') q).epi _
  have hδ : δ = 0 := h₁.epi_f_iff.1 hepi
  have : Epi δ := h₂.epi_f (((F.rightAcyclic_of_injective J) q).eq_of_tgt _ _)
  rw [IsZero.iff_id_eq_zero, ← cancel_epi δ, hδ, comp_zero, zero_comp]

namespace Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  {r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)}

/-- **Injective modules are divisible**: if `r : R ⟶ R` is a monomorphism, it acts by an
epimorphism on every injective `R`-module `J`. Indeed `J` is a quotient of a flat module `P`, on
which `r` acts injectively, and `P ⟶ J` extends along `r_P`. -/
lemma epi_regularEndSMul_of_injective [Abelian.HasFunctorialFlatResolution C] [Mono r.hom]
    (J : Mod C R) [Injective J] : Epi (regularEndSMul r J) := by
  obtain ⟨Λ⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution (Mod C R))
  have : Epi (Λ.π.app J) := Λ.epi_π_app J
  have : Mono (regularEndSMul r ((Λ.F ⋙ ObjectProperty.flat.ι).obj J)) :=
    mono_regularEndSMul_of_flat _ (Λ.F.obj J).property
  obtain ⟨s, hs⟩ := Injective.factors (Λ.π.app J) (regularEndSMul r _)
  have : Epi (s ≫ regularEndSMul r J) := by
    rw [(regularEndSMul_naturality r (N := J) s).symm.trans hs]
    infer_instance
  exact epi_of_epi s _

omit [IsCommMonObj S] in
/-- If `r ≫ φ = 0`, then `r` acts by zero on the restriction of scalars of every `S`-module. -/
lemma regularEndSMul_comap_eq_zero (w : r.hom ≫ φ = 0) (N : Mod C S) :
    regularEndSMul r ((comap φ).obj N) = 0 := by
  have hr : r = regularLift (regular R) (η[R] ≫ r.hom) :=
    regular_hom_ext (one_comp_regularLift _ _).symm
  refine hom_ext _ _ ?_
  rw [hr, regularEndSMul_regularLift_hom, globalSmul_comap, Category.assoc, w, comp_zero,
    zero_hom, globalSmul, MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and `r` acts by zero on an `R`-module `N`,
then the unit `N ⟶ S ⊗_R N` is an isomorphism: `N` is the restriction of scalars of an
`S`-module. -/
lemma isIso_extendUnit_of_regularEndSMul_eq_zero (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (N : Mod C R) (h : regularEndSMul r N = 0) :
    IsIso (extendUnit φ N) := by
  obtain ⟨hex, hepi⟩ := exact_regularEndSMul_extendUnit w hφ N
  have : Mono (extendUnit φ N) := hex.mono_g h
  exact isIso_of_mono_of_epi _

omit [MonoidalPreadditive C] [IsCommMonObj R] [IsCommMonObj S] in
/-- If `φ : R ⟶ S` is an epimorphism, every `R`-linear map between restrictions of scalars of
`S`-modules is `S`-linear. -/
noncomputable def comapPreimage [Epi φ] {A B : Mod C S}
    (g : (comap φ).obj A ⟶ (comap φ).obj B) : A ⟶ B :=
  homMk g.hom (by
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight A.X) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight A.X)
    have : Epi (φ ▷ A.X) := (MonoidalCategory.tensorRight A.X).map_epi φ
    rw [← cancel_epi (φ ▷ A.X)]
    have h := act_hom g
    rw [act_comap_obj, act_comap_obj] at h
    rw [← Category.assoc, h]
    exact whisker_exchange_assoc _ _ _)

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C] [IsCommMonObj R]
  [IsCommMonObj S] in
@[simp]
lemma comap_map_comapPreimage [Epi φ] {A B : Mod C S}
    (g : (comap φ).obj A ⟶ (comap φ).obj B) : (comap φ).map (comapPreimage g) = g :=
  hom_ext _ _ rfl

/-- **Restrictions of scalars of injective `S`-modules are acyclic**: if
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact and `F` is an additive functor on `R`-modules for
which the kernel `J[r]` of the action of `r` on every injective `R`-module `J` is `F`-acyclic,
then the restriction of scalars of every injective `S`-module `I` is `F`-acyclic. Indeed, for an
embedding `I ⟶ J` into an injective `R`-module, `I` embeds into the `S`-module `J[r]`, hence is a
direct summand of it. -/
theorem rightAcyclic_comap_of_injective {D : Type*} [Category* D] [Abelian D]
    (F : Mod C R ⥤ D) [F.Additive] (w : r.hom ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)
    (hF : ∀ (J : Mod C R) [Injective J], F.rightAcyclic (Limits.kernel (regularEndSMul r J)))
    (I : Mod C S) [Injective I] : F.rightAcyclic ((comap φ).obj I) := by
  have : Epi φ := hφ.epi_g
  let J := Injective.under ((comap φ).obj I)
  let m : (comap φ).obj I ⟶ J := Injective.ι _
  let K := Limits.kernel (regularEndSMul r J)
  have hm : m ≫ regularEndSMul r J = 0 := by
    rw [← regularEndSMul_naturality, regularEndSMul_comap_eq_zero w, zero_comp]
  let k : (comap φ).obj I ⟶ K := Limits.kernel.lift _ m hm
  have : Mono k := mono_of_mono_fac (Limits.kernel.lift_ι _ m hm)
  have hK : regularEndSMul r K = 0 := by
    rw [← cancel_mono (Limits.kernel.ι (regularEndSMul r J)), regularEndSMul_naturality,
      Limits.kernel.condition, zero_comp]
  have := isIso_extendUnit_of_regularEndSMul_eq_zero w hφ K hK
  let e : K ≅ (comap φ).obj (extendScalarsObj φ K) := asIso (extendUnit φ K)
  let k' : I ⟶ extendScalarsObj φ K := comapPreimage (k ≫ e.hom)
  have : Mono k' := by
    have : Mono ((comap φ).map k') := by
      rw [comap_map_comapPreimage]
      infer_instance
    have : Mono ((forget R).map ((comap φ).map k')) := (forget R).map_mono _
    exact (forget S).mono_of_mono_map this
  let ρ : extendScalarsObj φ K ⟶ I := Injective.factorThru (𝟙 I) k'
  have hρ : comapPreimage (k ≫ e.hom) ≫ ρ = 𝟙 I := Injective.comp_factorThru _ _
  have hi : k ≫ e.hom ≫ (comap φ).map ρ = 𝟙 _ := by
    rw [← Category.assoc, ← comap_map_comapPreimage (k ≫ e.hom), ← Functor.map_comp, hρ,
      Functor.map_id]
  intro q
  have : Mono ((F.rightDerived (q + 1)).map k) := by
    have h := congrArg (F.rightDerived (q + 1)).map hi
    rw [Functor.map_comp, Functor.map_id] at h
    have : IsSplitMono ((F.rightDerived (q + 1)).map k) := IsSplitMono.mk' ⟨_, h⟩
    infer_instance
  exact (hF J q).of_mono ((F.rightDerived (q + 1)).map k)

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward `f_*` of module objects preserves injective objects, being right adjoint to
the exact functor `f^*`. -/
instance injective_lowerStar_obj
    (J : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) [Injective J] :
    Injective ((f)_*⟦Λ⟧.obj J) :=
  Injective.injective_of_adjoint (upperStarLowerStarAdjunction Λ f) J

variable [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

omit [IsCommMonObj Λ] in
/-- If `Λ_X` is flat, the underlying abelian sheaf of an `f_*`-acyclic `Λ_X`-module is
`f_*`-acyclic. -/
lemma rightAcyclic_forget_of_rightAcyclic_lowerStar
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ((f)_*⟦Λ⟧).rightAcyclic M) : ((f)_*[Ab.{u + 1}]).rightAcyclic M.X := fun q ↦ by
  have : IsIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv (q + 1)) := by
    rw [show (lowerStarForgetIso Λ f).inv = (Iso.refl _ :
      (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}]).hom from rfl]
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have := isIso_rightDerivedLowerStarPlusForget Λ f
    have : IsIso ((rightDerivedLowerStarPlusForget Λ f).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := inferInstance
    unfold rightDerivedLowerStarPlusForget at this
    infer_instance
  exact ((Mod.forget _).map_isZero (h q)).of_iso
    ((asIso (Functor.rightDerivedBaseChange (lowerStarForgetIso Λ f).inv (q + 1))).app M).symm

end

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
  (f : X ⟶ Y)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- For a uniformizer `ϖ` and an injective `𝒪_{E,X}`-module `J`, the kernel `J[ϖ]` of the action
of `ϖ` on `J` is `f_*`-acyclic: `0 ⟶ J[ϖ] ⟶ J --ϖ--> J ⟶ 0` is short exact and stays so after
`f_*`, injective modules being divisible and `f_*` preserving injective modules. -/
lemma rightAcyclic_lowerStar_kernel (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (J : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) [Injective J] :
    ((f)_*⟦_⟧).rightAcyclic
      (Limits.kernel (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J)) := by
  have := mono_padicIntegersRegularEnd_hom X ℓ E ϖ hϖ
  have := Mod.epi_regularEndSMul_of_injective (r := padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J
  refine Functor.rightAcyclic_kernel_of_injective _ ?_
  have h : (f)_*⟦_⟧.map (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) J) =
      Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj J) :=
    Mod.hom_ext _ _ (lowerStar_map_regularEndSMul ℓ E ϖ f J)
  rw [h]
  have := mono_padicIntegersRegularEnd_hom Y ℓ E ϖ hϖ
  exact Mod.epi_regularEndSMul_of_injective _

/-- **The restriction of scalars to `𝒪_{E,X}` of an injective `𝔽_{E,X}`-module is
`f_*`-acyclic.** -/
lemma rightAcyclic_lowerStar_comap_of_injective
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E)) [Injective I] :
    ((f)_*⟦_⟧).rightAcyclic ((Mod.comap (padicIntegersToResidueField X ℓ E)).obj I) := by
  obtain ⟨ϖ, hϖ, -⟩ := exists_shortExact_padicIntegersMulLeft_residueField X ℓ E
  exact Mod.rightAcyclic_comap_of_injective _
    (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ)
    (fun J _ ↦ rightAcyclic_lowerStar_kernel ℓ E f ϖ hϖ J) I

/-- **`R⁺f_*` commutes with restriction of scalars along `𝒪_E ⟶ 𝔽_E`**: the base change morphism
`res R⁺f_* K ⟶ R⁺f_*(res K)` attached to `f_* ∘ res ≅ res ∘ f_*` is an isomorphism, restriction
of scalars sending injective `𝔽_{E,X}`-modules to `f_*`-acyclic `𝒪_{E,X}`-modules. -/
instance isIso_rightDerivedFunctorPlusBaseChange_comapLowerStarIso_residueField :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (comapLowerStarIso (Profinite.padicIntegersRingObjToResidueField ℓ E) f).hom) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_lowerStar_comap_of_injective ℓ E f I

/-- **Higher direct images commute with restriction of scalars along `𝒪_E ⟶ 𝔽_E`**: the base
change morphism `res R^q f_* M ⟶ R^q f_*(res M)` is an isomorphism. -/
instance isIso_rightDerivedBaseChange_comapLowerStarIso_residueField (q : ℕ) :
    IsIso (Functor.rightDerivedBaseChange
      (comapLowerStarIso (Profinite.padicIntegersRingObjToResidueField ℓ E) f).hom q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [Functor.rightDerivedBaseChange_app]
  infer_instance

/-- **An `𝔽_{E,X}`-module is `f_*`-acyclic as soon as its restriction of scalars to `𝒪_{E,X}`
is.** -/
theorem rightAcyclic_lowerStar_of_comap
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))
    (hM : ((f)_*⟦_⟧).rightAcyclic ((Mod.comap (padicIntegersToResidueField X ℓ E)).obj M)) :
    ((f)_*⟦Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E)⟧).rightAcyclic
      M := fun q ↦ by
  have hz : IsZero ((Mod.comap (padicIntegersToResidueField Y ℓ E)).obj
      ((((f)_*⟦_⟧).rightDerived (q + 1)).obj M)) :=
    (hM q).of_iso ((asIso (Functor.rightDerivedBaseChange
      (comapLowerStarIso (Profinite.padicIntegersRingObjToResidueField ℓ E) f).hom
        (q + 1))).app M)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact (Mod.comap _).map_injective (by rw [CategoryTheory.Functor.map_id, Functor.map_zero, hz])

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The underived (Push) comparison for `𝒪_E ⟶ 𝔽_E`** is an isomorphism at an `f_*`-acyclic
`𝒪_{E,X}`-module `M` on which a uniformizer `ϖ` acts injectively. -/
theorem isIso_pushHom_residueField_app_of_rightAcyclic (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    [Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)]
    (hM : ((f)_*⟦_⟧).rightAcyclic M) :
    IsIso ((pushHom (Profinite.padicIntegersRingObjToResidueField ℓ E) f).app M) :=
  isIso_pushHom_residueField_app_of_mono ℓ E ϖ f hϖ M
    (rightAcyclic_forget_of_rightAcyclic_lowerStar _ f hM)

end AlgebraicGeometry.ProEtale.CondensedRing
