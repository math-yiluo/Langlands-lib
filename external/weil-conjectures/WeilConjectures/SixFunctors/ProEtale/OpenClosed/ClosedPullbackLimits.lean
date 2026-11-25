/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections

/-!
# The closed inverse image preserves limits

Let `i : Z = Spec (A ⧸ I) ⟶ X = Spec A` be a closed immersion with quasi-compact open complement.
The pullback `i^*` of pro-étale sheaves of modules preserves all limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_closedSpecι`, blueprint
`proposition-extension-zero-restriction-closed-subscheme`).

The objects `V = Spec C̄` of `Z_proét` with `C̄` w-contractible and ind-étale over `A ⧸ I` are
weakly contractible and cover `Z_proét`
(`AlgebraicGeometry.ProEtale.exists_closedLiftBasis_cover`). On such `V = v(V) ×_X Z`, the
sections of `i^* F` are those of `F` over the henselian lift `v(V) = Spec H_A(C̄)`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), and these commute with limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A)

section Basis

variable (S : Type u) [CommRing S] [Algebra (A ⧸ I) S] [Algebra A S] [IsScalarTower A (A ⧸ I) S]
  [Algebra.IndEtale (A ⧸ I) S]

/-- The reduction isomorphism `H_A(C̄) ⊗_A (A ⧸ I) ≃ C̄`. -/
noncomputable def closedLiftTensorEquiv :
    TensorProduct A (Algebra.ClosedLift A S) (A ⧸ I) ≃+* S :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Algebra.ClosedLift A S)
    I).symm.toRingEquiv.trans
    (RingEquiv.ofBijective _ (Algebra.ClosedLift.bijective_reduction A S I))

/-- `closedLiftTensorEquiv` sends `1 ⊗ r` to the image of `r` in `C̄`. -/
lemma closedLiftTensorEquiv_one_tmul (r : A ⧸ I) :
    closedLiftTensorEquiv I S (1 ⊗ₜ r) = algebraMap (A ⧸ I) S r := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp only [closedLiftTensorEquiv, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, Algebra.smul_def, mul_one,
    RingEquiv.ofBijective_apply]
  change Algebra.ClosedLift.toAlgHom A S (algebraMap A _ r) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) S]
  rfl

/-- The base change `v(V) ×_X Z` of the henselian lift `v(V) = Spec H_A(C̄)` is `V = Spec C̄`. -/
noncomputable def closedLiftSpecPullbackIso :
    Spec (.of S) ≅ pullback (closedLiftSpec A S).hom (closedSpecι I) :=
  haveI : IsIso (CommRingCat.ofHom (closedLiftTensorEquiv I S :
      TensorProduct A (Algebra.ClosedLift A S) (A ⧸ I) →+* S)) :=
    inferInstanceAs (IsIso (closedLiftTensorEquiv I S).toCommRingCatIso.hom)
  asIso (Spec.map (CommRingCat.ofHom (closedLiftTensorEquiv I S :
      TensorProduct A (Algebra.ClosedLift A S) (A ⧸ I) →+* S))) ≪≫
    (pullbackSpecIso A (Algebra.ClosedLift A S) (A ⧸ I)).symm

/-- The first projection of `closedLiftSpecPullbackIso` is induced by the reduction map
`H_A(C̄) ⟶ C̄`. -/
lemma closedLiftSpecPullbackIso_hom_fst :
    (closedLiftSpecPullbackIso I S).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom A S :
        Algebra.ClosedLift A S →+* S)) := by
  simp only [closedLiftSpecPullbackIso, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp only [closedLiftTensorEquiv, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, RingEquiv.ofBijective_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, one_smul]
  rfl

/-- The second projection of `closedLiftSpecPullbackIso` is the structure morphism
`Spec C̄ ⟶ Spec (A ⧸ I)`. -/
lemma closedLiftSpecPullbackIso_hom_snd :
    (closedLiftSpecPullbackIso I S).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) S)) := by
  simp only [closedLiftSpecPullbackIso, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact closedLiftTensorEquiv_one_tmul I S r

end Basis

/-- The basis object `v(V) ×_X Z` attached to an `A ⧸ I`-algebra `C̄`. -/
noncomputable def closedLiftBasisObj (S : Type u) [CommRing S] [Algebra (A ⧸ I) S] :
    (Spec (.of (A ⧸ I))).ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedSpecι I)).obj
    (@closedLiftSpec A S _ (Algebra.compHom S (algebraMap A (A ⧸ I))))

/-- `v(V) ×_X Z ≅ V = Spec C̄`, for `C̄` ind-étale over `A ⧸ I`. -/
noncomputable def closedLiftBasisIso (S : Type u) [CommRing S] [Algebra (A ⧸ I) S]
    [Algebra.IndEtale (A ⧸ I) S] : Spec (.of S) ≅ (closedLiftBasisObj I S).left :=
  let : Algebra A S := Algebra.compHom S (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) S := .of_algebraMap_eq' rfl
  closedLiftSpecPullbackIso I S

/-- The objects `v(V) ×_X Z ≅ Spec C̄` of `Z_proét`, for `C̄` w-contractible and ind-étale over
`A ⧸ I`. -/
def IsClosedLiftBasis (V : (Spec (.of (A ⧸ I))).ProEt) : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra (A ⧸ I) S), Algebra.IndEtale (A ⧸ I) S ∧
    IsWContractibleRing S ∧ V = closedLiftBasisObj I S

/-- Under `closedLiftBasisIso`, the structure morphism of `v(V) ×_X Z` is the structure
morphism `Spec C̄ ⟶ Spec (A ⧸ I)`. -/
lemma closedLiftBasisIso_hom_comp (S : Type u) [CommRing S] [Algebra (A ⧸ I) S]
    [Algebra.IndEtale (A ⧸ I) S] :
    (closedLiftBasisIso I S).hom ≫ (closedLiftBasisObj I S).hom =
      Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) S)) := by
  let : Algebra A S := Algebra.compHom S (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) S := .of_algebraMap_eq' rfl
  exact closedLiftSpecPullbackIso_hom_snd I S

/-- A weakly étale `R`-algebra `C₀` has a faithfully flat ind-étale cover `S` which is
w-contractible and ind-étale over `R`. -/
lemma _root_.Algebra.WeaklyEtale.exists_isWContractibleRing_indEtale (R C₀ : Type u) [CommRing R]
    [CommRing C₀] [Algebra R C₀] [Algebra.WeaklyEtale R C₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C₀ S) (_ : Algebra R S)
      (_ : IsScalarTower R C₀ S), Algebra.IndEtale R S ∧ Module.FaithfullyFlat C₀ S ∧
        IsWContractibleRing S := by
  obtain ⟨T, _, _, _, _, hT₁, hT₂, hT₃⟩ := Algebra.WeaklyEtale.exists_indEtale R C₀
  obtain ⟨S, _, _, hS₁, hS₂, hS₃⟩ := exists_isWContractibleRing T
  let : Algebra C₀ S := Algebra.compHom S (algebraMap C₀ T)
  let : Algebra R S := Algebra.compHom S (algebraMap R T)
  have : IsScalarTower C₀ T S := .of_algebraMap_eq' rfl
  have : IsScalarTower R T S := .of_algebraMap_eq' rfl
  have : IsScalarTower R C₀ S := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R T S, IsScalarTower.algebraMap_apply R C₀ T,
      ← IsScalarTower.algebraMap_apply C₀ T S]
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.IndEtale.trans R T S, Module.FaithfullyFlat.trans C₀ T S, hS₃⟩

/-- The basis objects `v(V) ×_X Z ≅ Spec C̄` are weakly contractible. -/
lemma isWeaklyContractible_of_isClosedLiftBasis {V : (Spec (.of (A ⧸ I))).ProEt}
    (hV : IsClosedLiftBasis I V) : (ProEt.topology _).IsWeaklyContractible.{u + 1} V := by
  obtain ⟨S, _, _, _, _, rfl⟩ := hV
  exact Scheme.ProEt.isWeaklyContractible_of_iso (R := .of S) (closedLiftBasisIso I S).symm

/-- **The basis objects cover.** Every object of `(Spec (A ⧸ I))_proét` is covered by objects
`v(V) ×_X Z ≅ Spec C̄` with `C̄` w-contractible and ind-étale over `A ⧸ I`: cover it by affine
opens `Spec C₀`, and each `Spec C₀` by `Spec C̄` for a faithfully flat ind-étale w-contractible
`C₀`-algebra `C̄` which is ind-étale over `A ⧸ I`. -/
lemma exists_closedLiftBasis_cover (V : (Spec (.of (A ⧸ I))).ProEt) :
    ∃ (ι : Type u) (W : ι → (Spec (.of (A ⧸ I))).ProEt) (f : ∀ k, W k ⟶ V),
      (∀ k, IsClosedLiftBasis I (W k)) ∧ Sieve.ofArrows W f ∈ ProEt.topology _ V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  have hθ (x : 𝒜.I₀) : ∃ θ : CommRingCat.of (A ⧸ I) ⟶ 𝒜.X x,
      Spec.map θ = 𝒜.f x ≫ V.hom := Spec.map_surjective _
  choose θ hθ using hθ
  have hwe (x : 𝒜.I₀) : letI := (θ x).hom.toAlgebra; Algebra.WeaklyEtale (A ⧸ I) (𝒜.X x) := by
    let := (θ x).hom.toAlgebra
    rw [← weaklyEtale_SpecMap_algebraMap_iff]
    change WeaklyEtale (Spec.map (θ x))
    rw [hθ]
    infer_instance
  choose S iS iC iR iT hind hff hw using fun x ↦
    letI := (θ x).hom.toAlgebra
    have := hwe x
    Algebra.WeaklyEtale.exists_isWContractibleRing_indEtale (A ⧸ I) (𝒜.X x)
  let κ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  let U (x : 𝒜.I₀) := Scheme.ProEt.ofOpenImmersion V (𝒜.f x)
  let g (x : 𝒜.I₀) : closedLiftBasisObj I (S x) ⟶ U x :=
    MorphismProperty.Over.homMk ((closedLiftBasisIso I (S x)).inv ≫ Spec.map (κ x)) (by
      let := (θ x).hom.toAlgebra
      change _ ≫ 𝒜.f x ≫ V.hom = _
      rw [Category.assoc, Iso.inv_comp_eq, closedLiftBasisIso_hom_comp, ← hθ x, ← Spec.map_comp]
      congr 1
      ext r
      exact (IsScalarTower.algebraMap_apply (A ⧸ I) (𝒜.X x) (S x) _).symm)
  have hgs (x : 𝒜.I₀) : Surjective (g x).left := by
    have : Surjective (Spec.map (κ x)) :=
      ((flat_and_surjective_SpecMap_iff (κ x)).2
        (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
    change Surjective ((closedLiftBasisIso I (S x)).inv ≫ Spec.map (κ x))
    infer_instance
  have hgq (x : 𝒜.I₀) : QuasiCompact (g x).left := by
    change QuasiCompact ((closedLiftBasisIso I (S x)).inv ≫ Spec.map (κ x))
    infer_instance
  refine ⟨𝒜.I₀, fun x ↦ closedLiftBasisObj I (S x),
    fun x ↦ g x ≫ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x),
    fun x ↦ ⟨S x, iS x, iR x, hind x, hw x, rfl⟩, ?_⟩
  have hU : Sieve.ofArrows U (fun x ↦ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x)) ∈
      ProEt.topology _ V :=
    Scheme.ProEt.mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
      (fun x ↦ Sieve.ofArrows_mk _ _ x)
  refine (ProEt.topology _).transitive hU _ fun Y c hc ↦ ?_
  obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hc
  rw [Sieve.pullback_comp]
  refine (ProEt.topology _).pullback_stable c ((ProEt.topology _).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (R := .singleton (g x)) ?_))
  · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
    rw [Sieve.pullback_apply, Category.assoc]
    exact (Sieve.ofArrows (fun x ↦ closedLiftBasisObj I (S x))
      (fun x ↦ g x ≫ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x))).downward_closed
      (Sieve.ofArrows_mk _ _ x) d
  · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    have : Surjective ((ProEt.forget _ ⋙ Over.forget _).map (g x)) := hgs x
    have : QuasiCompact ((ProEt.forget _ ⋙ Over.forget _).map (g x)) := hgq x
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (g x).left
        (U x).hom (U x).prop (by
          rw [MorphismProperty.Over.w (g x)]; exact (closedLiftBasisObj I (S x)).prop))

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]
  [QuasiCompact j]

/-- On a basis object `V = v(V) ×_X Z`, taking sections of `i^*` is taking sections over the
henselian lift `v(V)`: the unit of `i^* ⊣ i_*` is a natural isomorphism. Hence sections of
`i^* F` over `V` commute with limits in `F`. -/
lemma isIso_map_limit_post_of_isClosedLiftBasis
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    {J : Type (u + 1)} [Category.{u + 1} J]
    (D : J ⥤ Sheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R))
    {V : (Spec (.of (A ⧸ I))).ProEt} (hV : IsClosedLiftBasis I V) :
    IsIso ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V)).map
      (limit.post D (closedSpecι I)^*[ModuleCat.{u + 1} R])) := by
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
  have : ∀ F, IsIso (τ.app F) := fun F ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_unit_app_closedLiftSpec (C := S) j
        (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction S T) hij F)
  have : IsIso τ := NatIso.isIso_of_isIso_app _
  have : PreservesLimit D ((closedSpecι I)^*[ModuleCat.{u + 1} R] ⋙ EV) :=
    preservesLimit_of_natIso D (asIso τ)
  have h := limit.post_post D (closedSpecι I)^*[ModuleCat.{u + 1} R] EV
  have : IsIso (EV.map (limit.post D (closedSpecι I)^*[ModuleCat.{u + 1} R]) ≫
      limit.post (D ⋙ (closedSpecι I)^*[ModuleCat.{u + 1} R]) EV) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (limit.post (D ⋙ (closedSpecι I)^*[ModuleCat.{u + 1} R]) EV)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`), part (2),
for `X = Spec A`: let `i : Spec (A ⧸ I) ⟶ Spec A` be a closed immersion with quasi-compact open
complement `j`. The pullback `i^*` of pro-étale sheaves of modules preserves all small limits.
(It preserves all colimits, being a left adjoint, and is exact,
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`.)

The comparison map `i^*(lim F) ⟶ lim i^* F` is bijective on sections over the weakly contractible
basis objects `V = Spec C̄ ≅ v(V) ×_X Z`
(`AlgebraicGeometry.ProEtale.isIso_map_limit_post_of_isClosedLiftBasis`), which cover
`Z_proét` (`AlgebraicGeometry.ProEtale.exists_closedLiftBasis_cover`); so its kernel and
cokernel vanish. -/
theorem preservesLimitsOfSize_upperStar_closedSpecι
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base)) :
    PreservesLimitsOfSize.{u + 1, u + 1} ((closedSpecι I)^*[ModuleCat.{u + 1} R]) := by
  refine ⟨fun {J} _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  set c := limit.post D (closedSpecι I)^*[ModuleCat.{u + 1} R]
  let E (V : (Spec (.of (A ⧸ I))).ProEt) :=
    sheafToPresheaf (ProEt.topology (Spec (.of (A ⧸ I)))) (ModuleCat.{u + 1} R) ⋙
      (CategoryTheory.evaluation _ _).obj (op V)
  have hc : ∀ V, IsClosedLiftBasis I V → IsIso ((E V).map c) := fun V hV ↦
    isIso_map_limit_post_of_isClosedLiftBasis I j hij D hV
  have hmono : Mono c := by
    refine Preadditive.mono_of_isZero_kernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) (IsClosedLiftBasis I)
      (exists_closedLiftBasis_cover I) (kernel c)).2 fun V hV ↦ ?_
    have := hc V hV
    exact ModuleCat.subsingleton_of_isZero
      ((isZero_kernel_of_mono ((E V).map c)).of_iso (PreservesKernel.iso (E V) c))
  have hepi : Epi c := by
    refine Preadditive.epi_of_isZero_cokernel _ ?_
    refine (GrothendieckTopology.isZero_sheaf_iff_of_forall_exists (R := R) (IsClosedLiftBasis I)
      (exists_closedLiftBasis_cover I) (cokernel c)).2 fun V hV ↦ ?_
    have := hc V hV
    refine ⟨fun y y' ↦ ?_⟩
    have hsurj := surjective_app_of_isWeaklyContractible
      (isWeaklyContractible_of_isClosedLiftBasis I hV) (cokernel.π c)
    have hcsurj : Function.Surjective ((E V).map c) :=
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
    have hzero : ∀ z, (cokernel.π c).hom.app (op V) ((E V).map c z) = 0 := fun z ↦ by
      change ((E V).map (c ≫ cokernel.π c)) z = 0
      rw [cokernel.condition, Functor.map_zero]
      rfl
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨x', rfl⟩ := hsurj y'
    obtain ⟨z, rfl⟩ := hcsurj x
    obtain ⟨z', rfl⟩ := hcsurj x'
    rw [hzero, hzero]
  have : IsIso c := isIso_of_mono_of_epi c
  exact preservesLimit_of_isIso_post _ _

end ProEtale

end AlgebraicGeometry
