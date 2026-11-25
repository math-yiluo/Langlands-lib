/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# Restriction to the closed point of the trait through henselian lifts

Let `S = Spec k'⟦t⟧` and `i : Spec k' ⟶ S` the closed point. The closed point is the closed
subscheme `Spec (k'⟦t⟧ ⧸ (t))`, with quasi-compact open complement `Spec k'⟦t⟧[t⁻¹]`. Hence the
sections of `i^* F` over the w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras `C̄` are the
sections of `F` over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), and these cover the site of
the closed point. So a module object `F` over `Λ_S` vanishes after `i^*` as soon as its sections
over all such `W` vanish (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_of_forall`),
and a morphism becomes an isomorphism after `i^*` as soon as it is bijective on all such
sections (`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_of_forall`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section ClosedLift

variable {A : CommRingCat.{u}} (I : Ideal A) {R : Type (u + 1)} [Ring R]

/-- A morphism of pro-étale sheaves of modules on `Spec (A ⧸ I)` which is bijective on sections
over the basis objects `v(V) ×_X Z ≅ Spec C̄` (`AlgebraicGeometry.ProEtale.IsClosedLiftBasis`) is
an isomorphism: these objects are weakly contractible and cover, so the kernel and the cokernel
vanish. -/
lemma isIso_of_bijective_app_of_isClosedLiftBasis
    {F G : Sheaf (ProEt.topology (Spec (.of (A ⧸ I)))) (ModuleCat.{u + 1} R)} (ψ : F ⟶ G)
    (hψ : ∀ V, IsClosedLiftBasis I V → Function.Bijective (ψ.hom.app (op V))) : IsIso ψ := by
  let E (V : (Spec (.of (A ⧸ I))).ProEt) :=
    sheafToPresheaf (ProEt.topology (Spec (.of (A ⧸ I)))) (ModuleCat.{u + 1} R) ⋙
      (CategoryTheory.evaluation _ _).obj (op V)
  have hc (V) (hV : IsClosedLiftBasis I V) : IsIso ((E V).map ψ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hψ V hV)
  have hmono : Mono ψ := by
    refine Preadditive.mono_of_isZero_kernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) (IsClosedLiftBasis I)
      (exists_closedLiftBasis_cover I) (kernel ψ)).2 fun V hV ↦ ?_
    have := hc V hV
    exact ModuleCat.subsingleton_of_isZero
      ((isZero_kernel_of_mono ((E V).map ψ)).of_iso (PreservesKernel.iso (E V) ψ))
  have hepi : Epi ψ := by
    refine Preadditive.epi_of_isZero_cokernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) (IsClosedLiftBasis I)
      (exists_closedLiftBasis_cover I) (cokernel ψ)).2 fun V hV ↦ ?_
    refine ⟨fun y y' ↦ ?_⟩
    have hsurj := surjective_app_of_isWeaklyContractible
      (isWeaklyContractible_of_isClosedLiftBasis I hV) (cokernel.π ψ)
    have hzero (z : (E V).obj F) : (cokernel.π ψ).hom.app (op V) ((E V).map ψ z) = 0 := by
      change ((E V).map (ψ ≫ cokernel.π ψ)) z = 0
      rw [cokernel.condition, Functor.map_zero]
      rfl
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨x', rfl⟩ := hsurj y'
    obtain ⟨z, rfl⟩ := (hψ V hV).2 x
    obtain ⟨z', rfl⟩ := (hψ V hV).2 x'
    exact (hzero z).trans (hzero z').symm
  exact isIso_of_mono_of_epi ψ

variable {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j] [QuasiCompact j]

/-- Let `i : Spec (A ⧸ I) ⟶ Spec A` have quasi-compact open complement. A morphism `φ` of
pro-étale sheaves of modules on `Spec A` which is bijective on sections over the henselian lifts
`Spec H_A(C̄)` of all w-contractible ind-étale `A ⧸ I`-algebras `C̄` becomes an isomorphism after
`i^*`: on the basis objects `Spec C̄`, the sections of `i^* φ` are those of `φ` over
`Spec H_A(C̄)` (`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`). -/
lemma isIso_upperStar_closedSpecι_map_of_forall
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    {F G : Sheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R)} (φ : F ⟶ G)
    (hφ : ∀ (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Algebra A C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale (A ⧸ I) C], IsWContractibleRing C →
        Function.Bijective (φ.hom.app (op (closedLiftSpec A C)))) :
    IsIso ((closedSpecι I)^*[ModuleCat.{u + 1} R].map φ) := by
  refine isIso_of_bijective_app_of_isClosedLiftBasis I _ fun V hV ↦ ?_
  obtain ⟨S, _, _, _, hS, rfl⟩ := hV
  let : Algebra A S := Algebra.compHom S (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) S := .of_algebraMap_eq' rfl
  let EV := sheafToPresheaf (ProEt.topology (Spec (.of (A ⧸ I)))) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op (closedLiftBasisObj I S))
  let EW := sheafToPresheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op (closedLiftSpec A S))
  let τ : EW ⟶ (closedSpecι I)^*[ModuleCat.{u + 1} R] ⋙ EV :=
    Functor.whiskerRight (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (closedSpecι I)).unit
      EW
  have hτ (F) : IsIso (τ.app F) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_unit_app_closedLiftSpec (C := S) j
        (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction S T) hij F)
  have : IsIso (EW.map φ) := (ConcreteCategory.isIso_iff_bijective _).2 (hφ S hS)
  have h : ((closedSpecι I)^*[ModuleCat.{u + 1} R] ⋙ EV).map φ =
      inv (τ.app F) ≫ EW.map φ ≫ τ.app G := by
    rw [τ.naturality φ, IsIso.inv_hom_id_assoc]
  have : IsIso (((closedSpecι I)^*[ModuleCat.{u + 1} R] ⋙ EV).map φ) := by
    rw [h]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

/-- The abelian version of `AlgebraicGeometry.ProEtale.isIso_upperStar_closedSpecι_map_of_forall`,
through the identification of abelian groups with `ULift ℤ`-modules. -/
lemma isIso_upperStar_closedSpecι_map_of_forall_ab
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    {F G : Sheaf (ProEt.topology (Spec A)) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : ∀ (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Algebra A C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale (A ⧸ I) C], IsWContractibleRing C →
        Function.Bijective (φ.hom.app (op (closedLiftSpec A C)))) :
    IsIso ((closedSpecι I)^*[Ab.{u + 1}].map φ) := by
  let S := sheafComposeUliftIntModuleToAb (Spec A)
  let ε : S.inv ⋙ S ≅ 𝟭 _ := S.asEquivalence.counitIso
  have hψ : IsIso ((closedSpecι I)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].map (S.inv.map φ)) := by
    refine isIso_upperStar_closedSpecι_map_of_forall I j hij _ fun C _ _ _ _ _ hC ↦ ?_
    let EW := sheafToPresheaf (ProEt.topology (Spec A)) Ab.{u + 1} ⋙
      (CategoryTheory.evaluation _ _).obj (op (closedLiftSpec A C))
    have : IsIso (EW.map φ) := (ConcreteCategory.isIso_iff_bijective _).2 (hφ C hC)
    have : IsIso (EW.map ((S.inv ⋙ S).map φ) ≫ EW.map (ε.hom.app G)) := by
      rw [← EW.map_comp, ε.hom.naturality φ, Functor.id_map, EW.map_comp]
      infer_instance
    have : IsIso (EW.map ((S.inv ⋙ S).map φ)) :=
      IsIso.of_isIso_comp_right _ (EW.map (ε.hom.app G))
    have : IsIso (uliftIntModuleToAb.map ((S.inv.map φ).hom.app (op (closedLiftSpec A C)))) :=
      this
    have : IsIso ((S.inv.map φ).hom.app (op (closedLiftSpec A C))) :=
      isIso_of_reflects_iso _ uliftIntModuleToAb
    exact (ConcreteCategory.isIso_iff_bijective _).1 this
  have : IsIso ((sheafComposeUliftIntModuleToAb (Spec (.of (A ⧸ I)))).inv.map
      ((closedSpecι I)^*[Ab.{u + 1}].map φ)) :=
    (NatIso.isIso_map_iff (sheafComposeInverseCompUpperStarIso (closedSpecι I)) φ).1 hψ
  exact isIso_of_reflects_iso _ (sheafComposeUliftIntModuleToAb (Spec (.of (A ⧸ I)))).inv

end ClosedLift

/-- The closed subscheme `V(f) = Spec (A ⧸ (f))` and the basic open `D(f) = Spec A[f⁻¹]` are
complementary in `Spec A`. -/
lemma isCompl_range_closedSpecι_span_singleton {A : CommRingCat.{u}} (f : A) :
    IsCompl (Set.range (closedSpecι (Ideal.span {f})).base)
      (Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))).base) := by
  have h₁ : Set.range (closedSpecι (Ideal.span {f})).base = PrimeSpectrum.zeroLocus {f} := by
    rw [Spec.map_base]
    erw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
  have h₂ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))).base =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    rw [← Scheme.Hom.coe_opensRange, Hom.opensRange_localizationAway]
  rw [h₁, h₂, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact isCompl_compl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k']

/-- The henselian lift `W = Spec H_{k'⟦t⟧}(C̄)` of a `k'⟦t⟧ ⧸ (t)`-algebra `C̄`, as an object of
the pro-étale site of the trait. -/
noncomputable abbrev traitClosedLift (C : Type u) [CommRing C]
    [Algebra (PowerSeries k') C] : (trait k').ProEt :=
  closedLiftSpec (.of (PowerSeries k')) C

/-- The closed point of the trait factors through the closed immersion
`Spec (k'⟦t⟧ ⧸ (t)) ⟶ Spec k'⟦t⟧`. -/
lemma exists_traitClosedPoint_eq_comp_closedSpecι :
    ∃ g : Spec (.of k') ⟶ Spec (.of (PowerSeries k' ⧸
        Ideal.span {(PowerSeries.X : PowerSeries k')})),
      traitClosedPoint k' =
        g ≫ closedSpecι (A := .of (PowerSeries k')) (Ideal.span {PowerSeries.X}) := by
  have h (a : PowerSeries k') (ha : a ∈ Ideal.span {PowerSeries.X}) :
      PowerSeries.constantCoeff a = 0 := by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ PowerSeries.constantCoeff h)), ?_⟩
  rw [traitClosedPoint, closedSpecι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The abelian version of `isIso_upperStar_traitClosedPoint_map_of_forall`. -/
lemma isIso_upperStar_traitClosedPoint_map_of_forall_ab
    {F G : Sheaf (ProEt.topology (trait k')) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : ∀ (C : Type u) [CommRing C]
      [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra (PowerSeries k') C]
      [IsScalarTower (PowerSeries k')
        (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C],
      IsWContractibleRing C → Function.Bijective (φ.hom.app (op (traitClosedLift C)))) :
    IsIso ((traitClosedPoint k')^*[Ab.{u + 1}].map φ) := by
  obtain ⟨g, hg⟩ := exists_traitClosedPoint_eq_comp_closedSpecι (k' := k')
  have := isIso_upperStar_closedSpecι_map_of_forall_ab _
    (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k')
      (Localization.Away (PowerSeries.X : PowerSeries k')))))
    (isCompl_range_closedSpecι_span_singleton (A := .of (PowerSeries k')) PowerSeries.X) φ hφ
  rw [hg]
  exact (NatIso.isIso_map_iff (ProEtale.upperStarComp Ab.{u + 1} g _).symm φ).1
    (inferInstanceAs (IsIso ((g)^*[Ab.{u + 1}].map _)))

/-- A module object over `Λ_S` vanishes after restriction to the closed point of the trait if
its sections over the henselian lifts of all w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras
vanish. -/
theorem isZero_upperStar_traitClosedPoint_obj_of_forall
    (F : Mod (Sheaf (ProEt.topology (trait k')) Ab.{u + 1}) (condensedRingObj Λ (trait k')))
    (hF : ∀ (C : Type u) [CommRing C]
      [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra (PowerSeries k') C]
      [IsScalarTower (PowerSeries k')
        (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C],
      IsWContractibleRing C →
        Subsingleton (F.X.obj.obj (op (traitClosedLift C)))) :
    Limits.IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj F) := by
  have h := isIso_upperStar_traitClosedPoint_map_of_forall_ab (0 : F.X ⟶ F.X)
    fun C _ _ _ _ _ hC ↦
      have := hF C hC
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨y, Subsingleton.elim _ _⟩⟩
  rw [Functor.map_zero, isIsoZero_iff_source_target_isZero] at h
  exact isZero_of_isZero_X Λ (h.1.of_iso (upperStarObjXIso Λ _ F))

/-- A morphism of module objects over `Λ_S` becomes an isomorphism after restriction to the
closed point of the trait if it is bijective on sections over the henselian lifts of all
w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras. -/
theorem isIso_upperStar_traitClosedPoint_map_of_forall
    {F G : Mod (Sheaf (ProEt.topology (trait k')) Ab.{u + 1}) (condensedRingObj Λ (trait k'))}
    (φ : F ⟶ G)
    (hφ : ∀ (C : Type u) [CommRing C]
      [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra (PowerSeries k') C]
      [IsScalarTower (PowerSeries k')
        (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C],
      IsWContractibleRing C →
        Function.Bijective (φ.hom.hom.app (op (traitClosedLift C)))) :
    IsIso ((traitClosedPoint k')^*⟦Λ⟧.map φ) := by
  have : IsIso ((Mod.forget _).map ((traitClosedPoint k')^*⟦Λ⟧.map φ)) :=
    (NatIso.isIso_map_iff (upperStarForgetIso Λ (traitClosedPoint k')) φ).1
      (isIso_upperStar_traitClosedPoint_map_of_forall_ab φ.hom hφ)
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale.CondensedRing
