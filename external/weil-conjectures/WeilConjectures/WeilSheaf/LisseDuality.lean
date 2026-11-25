/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TransposePairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.AbelianIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Braided
public import WeilConjectures.WeilSheaf.Dual

/-!
# Duality of lisse `ℓ`-adic sheaves on an irreducible scheme

Let `Y` be an irreducible scheme. Kernels and cokernels of morphisms of lisse sheaves on `Y` are
lisse, and a nonzero lisse sheaf has nonzero stalks at every geometric point. Hence a morphism
of lisse sheaves is a monomorphism (an epimorphism) as soon as it is injective (surjective) on
the stalks at one geometric point. On these stalks, finite-dimensional, the evaluations induce
perfect pairings (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing`),
which gives:

- the transpose `E ⟶ B^∨` of a monomorphism `B ⟶ E^∨` of lisse sheaves is an epimorphism
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.epi_transpose`);
- the pullback of the dual of a lisse sheaf is the dual of the pullback
  (`AlgebraicGeometry.ProEtale.isIso_adicUpperStarDualComparison`);
- if `L` is a quotient of a lisse subsheaf of `E^∨`, then `L^∨` is a quotient of a lisse subsheaf
  of `E` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_constituent_of_constituent_dual`):
  the constituents of the dual of a lisse sheaf are the duals of its constituents.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} [IrreducibleSpace Y] {K : Type u} [Field K]
  [IsAlgClosed K]

omit [IrreducibleSpace Y] in
/-- The stalk functor at a geometric point preserves epimorphisms. -/
instance preservesEpimorphisms_stalkFunctor (s : Spec (.of K) ⟶ Y) :
    (stalkFunctor l s).PreservesEpimorphisms := by
  unfold stalkFunctor
  infer_instance

omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- The stalk functor at a point preserves monomorphisms. -/
instance preservesMonomorphisms_stalkFunctor (s : Spec (.of K) ⟶ Y) :
    (stalkFunctor l s).PreservesMonomorphisms := by
  unfold stalkFunctor
  infer_instance

/-- A morphism of lisse sheaves on an irreducible scheme is an epimorphism as soon as it is
surjective on the stalks at one geometric point: its cokernel is lisse, and a nonzero lisse sheaf
has nonzero stalks everywhere. -/
theorem IsAdicLisseSheaf.epi_of_surjective_stalkFunctor_map {F G : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (f : F ⟶ G) (s : Spec (.of K) ⟶ Y)
    (hf : Function.Surjective ((stalkFunctor l s).map f.hom).hom) : Epi f := by
  refine Preadditive.epi_of_isZero_cokernel f (by_contra fun h ↦ ?_)
  obtain ⟨a, b, hab⟩ := ((isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace hF hG f).2
    ).nontrivial_globalSections_upperStar_of_irreducibleSpace h K s
  have hπ : Function.Surjective ((stalkFunctor l s).map (cokernel.π f).hom).hom :=
    have : Epi (cokernel.π f).hom := (AdicSheaf.forget Y).map_epi (cokernel.π f)
    (ModuleCat.epi_iff_surjective _).1 ((stalkFunctor l s).map_epi _)
  have h0 (x : (stalkFunctor l s).obj F.X) :
      ((stalkFunctor l s).map (cokernel.π f).hom).hom (((stalkFunctor l s).map f.hom).hom x) =
        0 := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', cokernel.condition]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  obtain ⟨a', rfl⟩ := hπ a
  obtain ⟨b', rfl⟩ := hπ b
  obtain ⟨a'', rfl⟩ := hf a'
  obtain ⟨b'', rfl⟩ := hf b'
  exact hab ((h0 a'').trans (h0 b'').symm)

/-- A morphism of lisse sheaves on an irreducible scheme is a monomorphism as soon as it is
injective on the stalks at one geometric point: its kernel is lisse, and a nonzero lisse sheaf
has nonzero stalks everywhere. -/
theorem IsAdicLisseSheaf.mono_of_injective_stalkFunctor_map {F G : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) (hG : IsAdicLisseSheaf G) (f : F ⟶ G) (s : Spec (.of K) ⟶ Y)
    (hf : Function.Injective ((stalkFunctor l s).map f.hom).hom) : Mono f := by
  refine Preadditive.mono_of_isZero_kernel f (by_contra fun h ↦ ?_)
  obtain ⟨a, b, hab⟩ := ((isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace hF hG f).1
    ).nontrivial_globalSections_upperStar_of_irreducibleSpace h K s
  have hι : Function.Injective ((stalkFunctor l s).map (kernel.ι f).hom).hom :=
    have : Mono (kernel.ι f).hom := (AdicSheaf.forget Y).map_mono (kernel.ι f)
    (ModuleCat.mono_iff_injective _).1 ((stalkFunctor l s).map_mono _)
  have h0 (x : (stalkFunctor l s).obj (kernel f).X) :
      ((stalkFunctor l s).map f.hom).hom (((stalkFunctor l s).map (kernel.ι f).hom).hom x) =
        0 := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', kernel.condition]
    erw [Mod.zero_hom, Functor.map_zero]
    rfl
  exact hab (hι (hf ((h0 a).trans (h0 b).symm)))


omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- A nonempty scheme has a point with values in an algebraically closed field. -/
lemma exists_spec_isAlgClosed_hom (Y : Scheme.{u}) [Nonempty Y] :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K), Nonempty (Spec (.of K) ⟶ Y) := by
  let y := Classical.arbitrary Y
  exact ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y⟩⟩

/-- **The transpose of a monomorphism of lisse sheaves is an epimorphism.** For lisse sheaves
`B` and `E` on an irreducible scheme and a monomorphism `v : B ⟶ E^∨`, the transpose
`E ⟶ B^∨` is an epimorphism: on the stalks at a geometric point, which are finite-dimensional
and on which the evaluations induce perfect pairings, it is the restriction of linear forms
along the injective map `B_s ⟶ (E_s)^∨`. -/
theorem IsAdicLisseSheaf.epi_transpose {B E : AdicSheaf l Y} (hB : IsAdicLisseSheaf B)
    (hE : IsAdicLisseSheaf E) (v : B ⟶ (AdicSheaf.ihom E).obj (AdicSheaf.unit l Y)) [Mono v] :
    Epi (Mod.transpose v) := by
  obtain ⟨K, _, _, ⟨s⟩⟩ := exists_spec_isAlgClosed_hom Y
  refine hE.epi_of_surjective_stalkFunctor_map
    (hB.ihom (isAdicLisseSheaf_adicConstantSheaf Y)) _ s fun y ↦ ?_
  have : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor l s).obj E.X)) :=
    (hE.isAdicConstructibleSheaf.upperStar s).finiteDimensional_globalSections
  let θ := (asIso (unitSection l s)).symm.toLinearEquiv
  let DE := LinearEquiv.ofBijective _ (WeilCoefficients.bijective_dualLinearMap
    (hE.bijective_evaluationPairing s) θ)
  have hDB := WeilCoefficients.bijective_dualLinearMap (hB.bijective_evaluationPairing s) θ
  have : Mono v.hom := (AdicSheaf.forget Y).map_mono v
  have hI : Function.Injective ((stalkFunctor l s).map v.hom).hom :=
    (ModuleCat.mono_iff_injective _).1 ((stalkFunctor l s).map_mono _)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    ((WeilCoefficients.toModuleCat l).map ((stalkFunctor l s).map v.hom)).hom
    (LinearMap.ker_eq_bot.2 hI)
  let ψ := WeilCoefficients.dualLinearMap (Mod.evaluationPairing (stalkFunctor l s) B
    (AdicSheaf.unit l Y)) θ.toLinearMap y ∘ₗ g
  let e := (Module.evalEquiv (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((stalkFunctor l s).obj E.X))).symm
      (ψ ∘ₗ DE.symm.toLinearMap)
  have he (w) : WeilCoefficients.dualLinearMap (Mod.evaluationPairing (stalkFunctor l s) E
      (AdicSheaf.unit l Y)) θ.toLinearMap w e = ψ w := by
    have h := Module.apply_evalEquiv_symm_apply (f := DE w) (g := ψ ∘ₗ DE.symm.toLinearMap)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.ofBijective_apply] at h
  refine ⟨e, hDB.1 (LinearMap.ext fun u ↦ ?_)⟩
  rw [WeilCoefficients.dualLinearMap_apply, Mod.evaluationPairing_transpose,
    ← WeilCoefficients.dualLinearMap_apply, he]
  simp only [ψ, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun hg u


section Pullback

attribute [local instance] Sheaf.symmetricCategory

variable {Z : Scheme.{u}} (g : Z ⟶ Y)

omit [IrreducibleSpace Y] [IsAlgClosed K] in
variable (l) in
/-- The comparison `g^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(g^* G, ℚ̄_ℓ)` of the pullback of the dual with the
dual of the pullback, adjoint to
`g^* 𝓗om(G, ℚ̄_ℓ) ⊗ g^* G ≅ g^*(𝓗om(G, ℚ̄_ℓ) ⊗ G) ⟶ g^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
noncomputable def adicUpperStarDualComparison (G : AdicSheaf l Y) :
    (g)^*ᵃ[l].obj ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y)) ⟶
      (AdicSheaf.ihom ((g)^*ᵃ[l].obj G)).obj (AdicSheaf.unit l Z) :=
  (Mod.ihomAdjunction ((g)^*ᵃ[l].obj G)).homEquiv _ _
    ((adicUpperStarTensorLeftIso l g G).inv.app _ ≫
      (g)^*ᵃ[l].map ((Mod.ihomAdjunction G).counit.app (AdicSheaf.unit l Y)) ≫
      (adicUpperStarUnitIso l g).hom)

omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- The comparison of the pullback of the dual with the dual of the pullback is compatible with
the evaluations. -/
lemma uncurryHom_adicUpperStarDualComparison (G : AdicSheaf l Y) :
    Mod.uncurryHom (adicUpperStarDualComparison l g G) =
      μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y)).X G.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation G (AdicSheaf.unit l Y)) ≫
        (adicUpperStarUnitIso l g).hom.hom := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
    ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y)) G
  have h₃ : Mod.tensorπ ((g)^*ᵃ[l].obj ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y)))
      ((g)^*ᵃ[l].obj G) = μ (g)^*[WeilCoefficients.{u} l] _ _ ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ _ G) ≫
          ((adicUpperStarTensorLeftIso l g G).hom.app _).hom := by
    erw [h₁, IsIso.hom_inv_id_assoc]
    rfl
  rw [Mod.uncurryHom_eq, adicUpperStarDualComparison, Equiv.symm_apply_apply, Mod.comp_hom',
    Mod.comp_hom', h₃, Category.assoc, Category.assoc, ← Category.assoc
      ((adicUpperStarTensorLeftIso l g G).hom.app _).hom, ← Mod.comp_hom', Iso.hom_inv_id_app,
    Mod.id_hom', Category.id_comp, adicUpperStar_map_hom, ← Functor.map_comp_assoc]
  rfl


omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- On the stalks at a point `s`, the comparison of the pullback of the dual with the dual of the
pullback is compatible with the pairings induced by the evaluations. -/
lemma evaluationPairing_adicUpperStarDualComparison (G : AdicSheaf l Y) (s : Spec (.of K) ⟶ Z)
    (f : ((g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s).obj
      ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y)).X)
    (x : ((g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s).obj G.X) :
    Mod.evaluationPairing (stalkFunctor l s) ((g)^*ᵃ[l].obj G) (AdicSheaf.unit l Z)
        (((stalkFunctor l s).map (adicUpperStarDualComparison l g G).hom).hom f) x =
      ((stalkFunctor l s).map (adicUpperStarUnitIso l g).hom.hom).hom
        (Mod.evaluationPairing ((g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s) G
          (AdicSheaf.unit l Y) f x) := by
  have hm : (stalkFunctor l s).map (adicUpperStarDualComparison l g G).hom ▷ _ ≫
      μ (stalkFunctor l s) _ _ ≫
        (stalkFunctor l s).map (Mod.evaluation ((g)^*ᵃ[l].obj G) (AdicSheaf.unit l Z)) =
      μ ((g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s) _ _ ≫
        ((g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s).map
          (Mod.evaluation G (AdicSheaf.unit l Y)) ≫
        (stalkFunctor l s).map (adicUpperStarUnitIso l g).hom.hom := by
    have h := uncurryHom_adicUpperStarDualComparison g G
    rw [Mod.uncurryHom] at h
    rw [μ_natural_left_assoc, ← Functor.map_comp, h, Functor.map_comp, Functor.map_comp]
    rfl
  exact congrArg (fun m ↦ m.hom (f ⊗ₜ x)) hm


omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- **The pullback of the dual of a lisse sheaf is the dual of the pullback**: for `G` lisse and
`g : Z ⟶ Y` with `Z` irreducible, the comparison `g^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(g^* G, ℚ̄_ℓ)` is an
isomorphism. Both sides are lisse, so it suffices to check this on the stalks at one geometric
point `s`, where the evaluations induce perfect pairings: of `(g^* G)_s` and of `G_{g s}`. -/
theorem isIso_adicUpperStarDualComparison [IrreducibleSpace Z] {G : AdicSheaf l Y}
    (hG : IsAdicLisseSheaf G) : IsIso (adicUpperStarDualComparison l g G) := by
  obtain ⟨K, _, _, ⟨s⟩⟩ := exists_spec_isAlgClosed_hom Z
  have h₁ : IsAdicLisseSheaf ((g)^*ᵃ[l].obj ((AdicSheaf.ihom G).obj (AdicSheaf.unit l Y))) :=
    (hG.ihom (isAdicLisseSheaf_adicConstantSheaf Y)).upperStar g
  have h₂ : IsAdicLisseSheaf ((AdicSheaf.ihom ((g)^*ᵃ[l].obj G)).obj (AdicSheaf.unit l Z)) :=
    (hG.upperStar g).ihom (isAdicLisseSheaf_adicConstantSheaf Z)
  have hP₁ := (hG.upperStar g).bijective_evaluationPairing s
  let τ : stalkFunctor l (s ≫ g) ≅ (g)^*[WeilCoefficients.{u} l] ⋙ stalkFunctor l s :=
    Functor.isoWhiskerRight (upperStarComp _ s g) _ ≪≫ Functor.associator _ _ _
  have : NatTrans.IsMonoidal τ.hom := by
    dsimp only [τ, Iso.trans_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  have hP₂ := (Mod.bijective_evaluationPairing_iff_of_iso _ τ G (AdicSheaf.unit l Y)).1
    (hG.bijective_evaluationPairing (s ≫ g))
  let u := (stalkFunctor l s).mapIso ((Mod.forget _).mapIso (adicUpperStarUnitIso l g))
  have hu (y) : u.hom.hom (u.inv.hom y) = y := by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  have hrel := evaluationPairing_adicUpperStarDualComparison g G s
  have hinj : Function.Injective
      ((stalkFunctor l s).map (adicUpperStarDualComparison l g G).hom).hom := fun f f' h ↦
    hP₂.1 (LinearMap.ext fun x ↦ u.toLinearEquiv.injective (by
      have := LinearMap.congr_fun (congrArg (Mod.evaluationPairing (stalkFunctor l s) _ _) h) x
      rwa [hrel, hrel] at this))
  have hsurj : Function.Surjective
      ((stalkFunctor l s).map (adicUpperStarDualComparison l g G).hom).hom := fun w ↦ by
    obtain ⟨f, hf⟩ := hP₂.2 (u.inv.hom ∘ₗ Mod.evaluationPairing (stalkFunctor l s) _ _ w)
    refine ⟨f, hP₁.1 (LinearMap.ext fun x ↦ ?_)⟩
    rw [hrel, hf, LinearMap.comp_apply]
    exact hu _
  have := h₁.mono_of_injective_stalkFunctor_map h₂ _ s hinj
  have := h₁.epi_of_surjective_stalkFunctor_map h₂ _ s hsurj
  exact isIso_of_mono_of_epi _

end Pullback


omit [IrreducibleSpace Y] [IsAlgClosed K] in
/-- The dual `𝓗om(L, ℚ̄_ℓ) ⟶ 𝓗om(B, ℚ̄_ℓ)` of an epimorphism `B ⟶ L` is a monomorphism: a
morphism into `𝓗om(L, ℚ̄_ℓ)` is determined by its transpose. -/
instance mono_ihomMap_app_of_epi {B L : AdicSheaf l Y} (p : B ⟶ L) [Epi p] (N : AdicSheaf l Y) :
    Mono ((Mod.ihomMap p).app N) :=
  Preadditive.mono_of_cancel_zero _ fun h hh ↦ by
    rw [← Mod.transpose_eq_zero_iff, ← cancel_epi p, comp_zero, ← Mod.transpose_comp_ihomMap,
      hh, Mod.transpose_zero]

/-- **Constituents of the dual.** Let `E`, `B`, `L` be lisse sheaves on an irreducible scheme.
If `L` is a quotient of a lisse subsheaf `B` of the dual `E^∨`, then the dual `L^∨` is a quotient
of a lisse subsheaf of `E`: the preimage of `L^∨ ⊆ B^∨` under the epimorphism `E ⟶ B^∨`
transposed to `B ⊆ E^∨` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.epi_transpose`). -/
theorem IsAdicLisseSheaf.exists_constituent_of_constituent_dual {E B L : AdicSheaf l Y}
    (hE : IsAdicLisseSheaf E) (hB : IsAdicLisseSheaf B) (hL : IsAdicLisseSheaf L)
    (i : B ⟶ (AdicSheaf.ihom E).obj (AdicSheaf.unit l Y)) [Mono i] (p : B ⟶ L) [Epi p] :
    ∃ (B' : AdicSheaf l Y) (i' : B' ⟶ E) (p' : B' ⟶ (AdicSheaf.ihom L).obj (AdicSheaf.unit l Y)),
      IsAdicLisseSheaf B' ∧ Mono i' ∧ Epi p' := by
  have := hB.epi_transpose hE i
  have hc := isAdicLisseSheaf_adicConstantSheaf (l := l) Y
  refine ⟨pullback (Mod.transpose i) ((Mod.ihomMap p).app (AdicSheaf.unit l Y)),
    pullback.fst _ _, pullback.snd _ _, ?_, inferInstance, inferInstance⟩
  have e : kernel (biprod.desc (Mod.transpose i) (-(Mod.ihomMap p).app (AdicSheaf.unit l Y))) ≅
      pullback (Mod.transpose i) ((Mod.ihomMap p).app (AdicSheaf.unit l Y)) :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _)
  exact (isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace (hE.biprod (hL.ihom hc))
    (hB.ihom hc) _).1.of_iso e

end AlgebraicGeometry.ProEtale
