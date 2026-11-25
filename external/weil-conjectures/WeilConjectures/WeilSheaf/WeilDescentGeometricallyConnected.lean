/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.WeilGroupContinuousExtension
public import WeilConjectures.WeilSheaf.WeilDescentPullbackRepresentation

/-!
# Irreducible lisse Weil sheaves on geometrically connected schemes come from the model

Let `V₀` be a smooth, separated, geometrically connected scheme of finite type over a finite
field `k₀`, with geometric fibre `p : V̄ ⟶ V₀`. By Deligne (Weil II, 1.3.14), every irreducible
lisse Weil sheaf `G` on `V₀` is a constant twist `p^* H ⊗ 𝓑_b` of the pullback of a lisse
`ℓ`-adic sheaf `H` on `V₀` with its canonical Weil structure
(`IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_geometricallyConnected`).

The proof:
1. Fix a `k̄`-rational base point `t` of `V̄`, a path `β : F_t ≅ F_{t ≫ Fr}` and the monodromies
   of lisse sheaves on `V̄` and `V₀` given by universal covers, which are compatible with `p`.
2. Weil II 1.3.14
   (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_isBoundedOn_fundamentalRep_twist`):
   `G ≅ Y ⊗ 𝓑_b` up to representations, with `Y` a lisse Weil sheaf whose Weil fundamental
   representation `ρ_Y` of `π₁(V̄, t) ⋊ ℤ` is bounded.
3. `ρ_Y` extends to a continuous representation `σ` of `π₁(V₀, t ≫ p)` along
   `arithHom : π₁(V̄, t) ⋊ ℤ → π₁(V₀, t ≫ p)`
   (`Representation.exists_continuous_extension_of_isBoundedOn`,
   with the homotopy exact sequence, `AlgebraicGeometry.FrobeniusBasePoint.denseRange_arithHom`
   etc.); `σ` is the monodromy representation of a lisse sheaf `H` on `V₀`.
4. The Weil fundamental representation of `p^* H` is `σ ∘ arithHom`
   (`AlgebraicGeometry.FrobeniusBasePoint.pullbackStalkEquiv_fundamentalRep`), so `p^* H ⊗ 𝓑_b`
   and `G` have isomorphic Weil fundamental representations
   (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep_constantTwist`), hence are
   isomorphic (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.nonempty_iso_of_linearEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale Scheme.FiniteEtale FrobeniusBasePoint

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [Smooth (V ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]

/-- **Irreducible lisse Weil sheaves come from the model up to twist** (Deligne, Weil II,
1.3.14), for a smooth, separated, geometrically connected `k₀`-scheme `V₀` of finite type: every
irreducible lisse Weil sheaf is isomorphic to a constant twist `p^* H ⊗ 𝓑_b` of the pullback of
a lisse `ℓ`-adic sheaf `H` on `V₀`, with its canonical Weil structure. -/
theorem IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_geometricallyConnected
    {G : WeilSheaf k₀ l V} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := k₀) hH).constantTwist b) := by
  -- the geometric fibre and the model are connected, regular and noetherian
  have : ConnectedSpace (V ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    connectedSpace_geometricFiber
  have : Smooth (V ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (V ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have := IsRegular.of_smooth (V ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace V :=
    quasiSeparatedSpace_of_quasiSeparated (V ↘ Spec (CommRingCat.of k₀))
  have : Surjective (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj := by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))) :=
      ⟨fun _ ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.pullback_fst _ _ this
  have : ConnectedSpace V := by
    refine connectedSpace_iff_univ.2 ?_
    rw [← Set.range_eq_univ.2 (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.surjective]
    exact isConnected_range (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.continuous
  -- base point, monodromies
  obtain ⟨t, ht⟩ :=
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  let B : FrobeniusBasePoint k₀ V := ⟨t, (nonempty_iso_of_fiberFunctor _ _).some⟩
  have := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (CommRingCat.of k₀))
  have hM := universalLisseMonodromy_isEquivalenceAt l
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀ B.t
  have hM₀ := universalLisseMonodromy_isEquivalenceAt l V k₀
    (B.t ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
  have hc := isCompatible_universalLisseMonodromy l k₀
    (Y := V) (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  -- Weil II 1.3.14: a twist of `G` has bounded Weil fundamental representation
  obtain ⟨b, Y, e, he, -, hbdd⟩ := B.weilData.exists_isBoundedOn_fundamentalRep_twist _ hM hG
  have : FiniteDimensional (PadicAlgCl l)
      (LisseMonodromy.StalkSpace B.t (Y.obj.toLisse Y.property)) :=
    Y.obj.finiteDimensional_stalkObj B.t
  -- it extends continuously to `π₁(V₀, t ≫ p)`
  obtain ⟨σ, hσc, hσα⟩ := Representation.exists_continuous_extension_of_isBoundedOn
    B.weilData.deg B.weilData.deg_frobLift SemidirectProduct.inl
    (fun w hw ↦ by
      have : w ∈ (SemidirectProduct.inl : Aut (fiber B.t) →* B.WeilGroup).range := by
        rw [SemidirectProduct.range_inl_eq_ker_rightHom]
        exact hw
      exact this)
    B.arithHom (B.denseRange_arithHom ht)
    (by
      have : B.arithHom.comp SemidirectProduct.inl = B.geomAut :=
        MonoidHom.ext fun g ↦ B.arithHom_inl g
      rw [this]
      exact B.continuous_geomAut)
    (by
      have : B.arithHom.comp SemidirectProduct.inl = B.geomAut :=
        MonoidHom.ext fun g ↦ B.arithHom_inl g
      rw [this]
      exact B.geomAut_injective)
    (fun m hm ↦ B.exists_isOpen_dvd_deg ht m hm)
    (B.weilData.fundamentalRep _ Y.obj Y.property)
    (B.weilData.fundamentalRep_isContinuousOn _ Y.obj Y.property hM) hbdd
  -- `σ` is the monodromy representation of a lisse sheaf `H` on `V₀`
  obtain ⟨⟨H, hH⟩, eH, heH⟩ := hM₀.essSurj _ σ hσc
  have hF : (geometricFiberPullback (k₀ := k₀) hH).IsLisse := isLisse_geometricFiberPullback hH
  have hE₁ := B.pullbackStalkEquiv_fundamentalRep _ _ hc hF hH
    (geometricFiberPullbackCarrierIso hH) (adicFrobStr_geometricFiberPullback hH)
  -- `p^* H ⊗ 𝓑_b` and `G` have isomorphic Weil fundamental representations
  let E : LisseMonodromy.StalkSpace B.t
      ((geometricFiberPullback (k₀ := k₀) hH).toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG.1) :=
    ((B.pullbackStalkEquiv hF hH (geometricFiberPullbackCarrierIso hH)).symm.trans eH).trans e
  have hE (w : B.WeilGroup) (v) : E ((B.weilData.fundamentalRep
      (universalLisseMonodromy l (V ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀) _ hF).twist
      (Representation.degreeCharacter B.weilData.deg b) w v) =
        B.weilData.fundamentalRep
          (universalLisseMonodromy l (V ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀) G hG.1 w
          (E v) := by
    obtain ⟨x, rfl⟩ :=
      (B.pullbackStalkEquiv hF hH (geometricFiberPullbackCarrierIso hH)).surjective v
    simp only [E, LinearEquiv.trans_apply, Representation.twist_apply,
      Representation.degreeCharacter_apply, LinearMap.smul_apply, map_smul, ← hE₁,
      LinearEquiv.symm_apply_apply, heH]
    rw [hσα, he, Representation.twist_apply, Representation.degreeCharacter_apply,
      LinearMap.smul_apply, smul_smul, ← Units.val_mul, ← mul_zpow, mul_inv_cancel, one_zpow,
      Units.val_one,
      one_smul]
  obtain ⟨i⟩ := B.weilData.nonempty_constantTwist_iso_of_linearEquiv _ hM hF hG.1 b E hE
  exact ⟨H, hH, b, ⟨i.symm⟩⟩

end AlgebraicGeometry.WeilSheaf
