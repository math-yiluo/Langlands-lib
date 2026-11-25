/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.MiddleExtension
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Extending lisse Weil sheaves over points with trivial local monodromy

Let `j : U₀ ⟶ C₀` be a dense open immersion into a smooth curve over the finite field `k₀`, and
`F` a lisse Weil sheaf on `U₀`.

* If the underlying `ℓ`-adic sheaf of `F` on the geometric curve `Ū` is the restriction of a
  lisse sheaf `G` on `C̄`, then `F` is the restriction of a lisse Weil sheaf on `C₀`
  (`AlgebraicGeometry.WeilSheaf.exists_isLisse_upperStar_iso_of_adicUpperStar_iso`): the Weil
  structure `Fr^* F ≅ F` transported to `j̄^* Fr^* G ≅ j̄^* G` comes from a unique isomorphism
  `Fr^* G ≅ G`, since restriction to the dense open `Ū` is fully faithful on lisse sheaves.
* If the monodromy of `F` on `Ū` is trivial on the kernel of `π₁(Ū, t) → π₁(C̄, t)`, then `F` is
  the restriction of a lisse Weil sheaf on `C₀`
  (`AlgebraicGeometry.WeilSheaf.exists_isLisse_upperStar_iso_of_rep_eq_self`). For `C₀ = U₀ ∪ {x}`
  the kernel is the local inertia at `x`: a lisse sheaf with trivial local monodromy at `x`
  extends over `x` (blueprint `corollary-unramified-boundary-point--2`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open ProEtale Scheme.FiniteEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]

/-- **Weil structures descend from a dense open.** Let `j : U₀ ⟶ C₀` be a dense quasi-compact
open immersion into a smooth `k₀`-scheme, `F` a Weil sheaf on `U₀` and `G` a lisse `ℓ`-adic sheaf
on `C̄` with `j̄^* G ≅ F`. Then `G` carries a Weil structure making it a lisse Weil sheaf `G'` on
`C₀` with `j^* G' ≅ F`: the Weil structure of `F` transported to `j̄^* Fr^* G ≅ j̄^* G` is the
restriction of a unique isomorphism `Fr^* G ≅ G`, since `j̄^*` is fully faithful on lisse
sheaves (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.adicUpperStar_map_bijective`). -/
theorem exists_isLisse_upperStar_iso_of_adicUpperStar_iso
    [Smooth (C ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) (F : WeilSheaf k₀ l U)
    {G : AdicSheaf l (C ↘ Spec (CommRingCat.of k₀)).geometricFiber} (hG : IsAdicLisseSheaf G)
    (e : (Scheme.Hom.geometricFiberMap j (comp_over j _))^*ᵃ[l].obj G ≅ F.obj.carrier) :
    ∃ G' : WeilSheaf k₀ l C, G'.IsLisse ∧ Nonempty ((upperStar j).obj G' ≅ F) := by
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have hY := isRegularLocalRing_stalk_geometricFiber (C := C) (k₀ := k₀)
  have hd : Dense (Set.range jb.base) := Scheme.Hom.dense_range_geometricFiberMap j hj
  set FrC := frobeniusPullback k₀ l C
  set FrU := frobeniusPullback k₀ l U
  set α :=
    adicUpperStarGeometricFiberMapCompFrobeniusIso l j (comp_over j (Spec (CommRingCat.of k₀)))
  have hFrG : IsAdicLisseSheaf (FrC.obj G) :=
    (hG.upperStar _).of_iso ((adicUpperStarIsoLowerStarInv l _).app G)
  -- the Weil structure of `F`, transported to `j̄^* Fr^* G ≅ j̄^* G`
  let χ : (jb)^*ᵃ[l].obj (FrC.obj G) ≅ (jb)^*ᵃ[l].obj G :=
    α.symm.app G ≪≫ FrU.mapIso e ≪≫ F.obj.str ≪≫ e.symm
  obtain ⟨φ, hφ⟩ := (IsAdicLisseSheaf.adicUpperStar_map_bijective hY jb hd (FrC.obj G) hG).2 χ.hom
  obtain ⟨ψ, hψ⟩ := (IsAdicLisseSheaf.adicUpperStar_map_bijective hY jb hd G hFrG).2 χ.inv
  have h₁ : φ ≫ ψ = 𝟙 _ :=
    (IsAdicLisseSheaf.adicUpperStar_map_bijective hY jb hd (FrC.obj G) hFrG).1 (by
      rw [Functor.map_comp, hφ, hψ, Iso.hom_inv_id]; exact ((jb)^*ᵃ[l].map_id _).symm)
  have h₂ : ψ ≫ φ = 𝟙 _ :=
    (IsAdicLisseSheaf.adicUpperStar_map_bijective hY jb hd G hG).1 (by
      rw [Functor.map_comp, hφ, hψ, Iso.inv_hom_id]; exact ((jb)^*ᵃ[l].map_id _).symm)
  let str : FrC.obj G ≅ G := ⟨φ, ψ, h₁, h₂⟩
  let G' : WeilSheaf k₀ l C := ⟨IsoAlgebra.mk G str, hG.isAdicConstructibleSheaf⟩
  refine ⟨G', hG, ⟨ObjectProperty.isoMk _ (IsoAlgebra.isoMk e ?_)⟩⟩
  have hs : ((upperStar j).obj G').obj.str.hom = α.hom.app G ≫ (jb)^*ᵃ[l].map φ := by
    rw [upperStar_obj_obj_str]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, G', IsoAlgebra.mk_str,
      IsoAlgebra.mk_carrier, str]
    rfl
  rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, hs, hφ]
  simp only [χ, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_app_assoc]
  rfl

/-- **A lisse Weil sheaf with trivial monodromy on the kernel of `π₁(Ū) → π₁(C̄)` extends.** Let
`j : U₀ ⟶ C₀` be a dense open immersion into a smooth geometrically connected `k₀`-scheme of
finite type, `F` a lisse Weil sheaf on `U₀` and `t` a geometric point of the geometric fibre `Ū`.
If the monodromy representation of `F` on `Ū` at `t`
(`AlgebraicGeometry.ProEtale.universalLisseMonodromy`) is trivial on the kernel of
`π₁(Ū, t) → π₁(C̄, t)`, then `F` is the restriction of a lisse Weil sheaf on `C₀`: the underlying
sheaf extends to `C̄`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_rep_eq_self`, the map of
fundamental groups being surjective since `C̄` is regular), and so does the Weil structure
(`AlgebraicGeometry.WeilSheaf.exists_isLisse_upperStar_iso_of_adicUpperStar_iso`).

For `C₀ = U₀ ∪ {x}` the kernel is the local inertia at `x`: this is the extension of a lisse sheaf
with trivial local monodromy over `x`, used in blueprint
`corollary-unramified-boundary-point--2`. -/
theorem exists_isLisse_upperStar_iso_of_rep_eq_self [Smooth (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsLocallyNoetherian (U ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [CompactSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (U ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [ConnectedSpace (U ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (hFt : ∀ σ ∈ (pullbackPathHom (Scheme.Hom.geometricFiberMap j (comp_over j _)) t).ker,
      ∀ v, (universalLisseMonodromy l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀).rep t
        ⟨F.obj.carrier, hF⟩ σ v = v) :
    ∃ G' : WeilSheaf k₀ l C, G'.IsLisse ∧ Nonempty ((upperStar j).obj G' ≅ F) := by
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have : ConnectedSpace (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := C ↘ Spec (CommRingCat.of k₀))
      (Scheme.specAlgebraicClosure k₀).hom (C ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
      (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (IsPullback.of_hasPullback _ _)
  have : Smooth (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have hsurj : Function.Surjective (pullbackPathHom jb t) := fun σ ↦
    exists_pullbackPathIso_eq_of_isRegular jb t σ
  obtain ⟨G, ⟨i⟩⟩ := LisseMonodromy.exists_upperStar_iso_of_rep_eq_self
    (universalLisseMonodromy_isEquivalenceAt l _ k₀ (t ≫ jb))
    (universalLisseMonodromy_isEquivalenceAt l _ k₀ t)
    (isCompatible_universalLisseMonodromy l k₀ jb) hsurj hFt
  exact exists_isLisse_upperStar_iso_of_adicUpperStar_iso j hj F G.property
    ((ObjectProperty.ι _).mapIso i)

end AlgebraicGeometry.WeilSheaf
