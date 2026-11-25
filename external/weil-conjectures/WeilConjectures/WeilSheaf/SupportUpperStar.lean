/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# The support of the pullback of a Weil sheaf

The stalk of a Weil sheaf at a closed point `x` is nonzero exactly when its stalk at any geometric
point over `x` is (`AlgebraicGeometry.WeilSheaf.nontrivial_stalk_iff_nontrivial_stalkObj`): two
geometric points over `x` differ by a power of the geometric Frobenius up to reparametrisation.
Hence the support of a pullback `φ^* F` lies over the support of `F`
(`AlgebraicGeometry.WeilSheaf.mem_support_of_mem_support_upperStar`), and the pullback of `F` to
a scheme of finite type missing the support of `F` vanishes
(`AlgebraicGeometry.WeilSheaf.isZero_upperStar_of_forall_notMem_support`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The stalk of a Weil sheaf at a closed point `x` is nonzero if and only if its stalk at a
geometric point `s` over `x` is: the chosen geometric point over `x` and `s` differ by a power
of the geometric Frobenius, up to reparametrisation. -/
theorem nontrivial_stalk_iff_nontrivial_stalkObj (F : WeilSheaf k₀ l X) (x : X.finitePoints)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hs : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1) :
    Nontrivial (F.stalk x).carrier ↔
      Nontrivial ((WeilCoefficients.toModuleCat l).obj (F.stalkObj s)) := by
  have hx :=
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base x
  obtain ⟨g, j, -, hg, -⟩ :=
    (X ↘ Spec (CommRingCat.of k₀)).exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow s
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)
      (hs.trans hx.symm)
      (by rw [hs]; exact x.2)
  let e : F.stalkObj ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) ≅
      F.stalkObj s :=
    (F.stalkObjFrobeniusPowIso j _).symm ≪≫ eqToIso (congrArg F.stalkObj hg.symm) ≪≫
      (Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ g.hom s).app F.obj.carrier.X) ≪≫
        (ProEtale.globalSectionsUpperStarIso _ g).app _
  exact ⟨fun h ↦ @Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e).symm.toEquiv h,
    fun h ↦ @Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e).toEquiv h⟩

/-- The support of a pullback lies over the support: if the stalk of `φ^* F` at a closed point
`y` is nonzero, so is the stalk of `F` at `φ(y)`, the two being stalks at the same geometric
point. -/
theorem mem_support_of_mem_support_upperStar (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X) {y : Y.finitePoints} (hy : y ∈ ((upperStar φ).obj F).support) :
    (⟨φ.base y.1, Scheme.Hom.map_mem_finitePoints φ y.2⟩ : X.finitePoints) ∈ F.support := by
  have e := asIso (stalkObjHomOfUpperStar φ ((upperStar φ).obj F) (𝟙 _)
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y))
  have h1 : Nontrivial ((WeilCoefficients.toModuleCat l).obj (((upperStar φ).obj F).stalkObj
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y))) := hy
  refine (nontrivial_stalk_iff_nontrivial_stalkObj F _ _ ?_).2
    (@Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e).toEquiv h1)
  rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← Category.assoc,
    Scheme.Hom.comp_base, TopCat.comp_app,
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base]

/-- The pullback of a Weil sheaf `F` to a `k₀`-scheme `Y` locally of finite type whose closed
points all map outside the support of `F` vanishes: by
`AlgebraicGeometry.WeilSheaf.mem_support_of_mem_support_upperStar` its stalks at the closed points
vanish, and these detect zero objects. -/
theorem isZero_upperStar_of_forall_notMem_support
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (h : ∀ y : Y.finitePoints,
      (⟨φ.base y.1, Scheme.Hom.map_mem_finitePoints φ y.2⟩ : X.finitePoints) ∉ F.support) :
    IsZero ((upperStar φ).obj F) := by
  by_contra hz
  obtain ⟨y, hy⟩ := exists_nontrivial_stalk_of_not_isZero _ hz
  exact h y (mem_support_of_mem_support_upperStar φ F hy)

end AlgebraicGeometry.WeilSheaf
