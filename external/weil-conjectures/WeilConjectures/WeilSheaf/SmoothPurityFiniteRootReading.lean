/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
public import WeilConjectures.TateTwist.FiniteRootsOfUnity
public import WeilConjectures.TateTwist.RootsOfUnityUpperStar
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.WeilSheaf.SmoothPurityRootKernelPullback

/-! # The canonical root comparison and geometric pullback

The finite root site comparison already proves the geometric square. Here its
normalised root map is identified with the kernel map used by the Tate twist API.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
  {X Y : Scheme.{u}} (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))

/-- The normalized finite root pullback is the canonical map induced on kernels. -/
lemma purity_finiteEtaleRootPullback_eq :
    ((finiteEtaleTwistPullbackData A N hN hA).r g hY).hom =
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g := by
  apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
  rw [upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
  exact ((finiteEtaleTwistPullbackData A N hN hA).laws.2.1 g hY).symm

variable [Finite A]

include A hA

/-- Cartier comparison intertwines the canonical étale root pullback and the
pro-étale root pullback, for arbitrary scheme maps. -/
lemma purity_cartierRootsIso_pullback (hX : IsUnit (N : Γ(X, ⊤))) :
    (g)^*[Ab.{u + 1}].map (cartierRootsIso Y N hN hY).hom ≫
        proEtaleRootsOfUnityInverseImageMap g N =
      (comparisonCoefficientPullbackIso Ab.{u + 1} g).inv.app (Y.rootsOfUnitySheaf N) ≫
        ν^*(X)[Ab.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g) ≫
        (cartierRootsIso X N hN hX).hom := by
  obtain ⟨σ, δ, h⟩ := finiteRootSiteComparison A
  have hroot := h.2.2.2.2.2.2.1 N hN hA g hY hX
  rw [purity_finiteEtaleRootPullback_eq] at hroot
  exact hroot

/-- The comparison used in finite Tate reduction commutes with the canonical
geometric root datum on both sites. -/
lemma purity_comparisonUpperStarRootsOfUnityIso_pullback (hX : IsUnit (N : Γ(X, ⊤))) :
    (g)^*[Ab.{u + 1}].map (comparisonUpperStarRootsOfUnityIso Y N hN hY).hom ≫
        upperStarRootsOfUnitySheafHom g N =
      (comparisonCoefficientPullbackIso Ab.{u + 1} g).inv.app (Y.rootsOfUnitySheaf N) ≫
        ν^*(X)[Ab.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g) ≫
        (comparisonUpperStarRootsOfUnityIso X N hN hX).hom := by
  apply (cancel_mono (rootsOfUnitySheafIsoKernel X N).hom).mp
  simp only [comparisonUpperStarRootsOfUnityIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← purity_rootsOfUnitySheafIsoKernel_upperStar]
  rw [← (g)^*[Ab.{u + 1}].map_comp_assoc
      (rootsOfUnitySheafIsoKernel Y N).inv (rootsOfUnitySheafIsoKernel Y N).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact purity_cartierRootsIso_pullback A N hN hA g hY hX

end AlgebraicGeometry.ProEtale
