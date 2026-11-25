/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentStalkColimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# A sheaf on a limit of schemes is the colimit of the pullbacks of its pushforwards

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, with projections `pᵢ : X ⟶ Xᵢ`. For every étale sheaf `F` of `Λ`-modules on
`X`, the canonical map `colimᵢ pᵢ^* pᵢ_* F ⟶ F` is an isomorphism
(`AlgebraicGeometry.Etale.isColimitDescentCocone`, Stacks 0EYN).

The diagram `i ↦ pᵢ^* pᵢ_* F` is `AlgebraicGeometry.Etale.descentDiagram`, and the cocone of
counits is `AlgebraicGeometry.Etale.descentCocone`.

The proof checks the statement on geometric stalks. The stalk of `pᵢ^* pᵢ_* F` at a geometric
point `x̄` of `X` is the stalk of `pᵢ_* F` at `pᵢ ∘ x̄`, that is, the colimit of the sections
`F(V ×_{Xᵢ} X)` over the étale neighbourhoods `V` of `pᵢ ∘ x̄`; every étale neighbourhood of
`x̄` in `X` is refined by one of this form, and so are the morphisms between them, by the
descent of affine étale schemes and of morphisms of finite presentation along the limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} {c : Cone D}

variable (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))

instance : HasColimitsOfShape Iᵒᵖ (Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Sheaf.instHasColimitsOfShape

include hc in
/-- Blueprint `corollary-open-direct-image-over-field--2`: **a sheaf on a limit of schemes is the
colimit of the pullbacks of its pushforwards** (Stacks 0EYN). Let `X = lim Xᵢ` be a cofiltered limit
of quasi-compact quasi-separated schemes (for example affine schemes, or quasi-compact opens of
affine schemes) with affine transition maps, and write `pᵢ : X ⟶ Xᵢ`. For every étale sheaf
`F` of `Λ`-modules on `X`, the canonical map `colimᵢ pᵢ^* pᵢ_* F ⟶ F` induced by the counits
`pᵢ^* pᵢ_* F ⟶ F` is an isomorphism. Here `i ↦ pᵢ^* pᵢ_* F` is
`AlgebraicGeometry.Etale.descentDiagram`. -/
theorem isIso_colimitDesc_descentCocone :
    IsIso (colimit.desc _ (descentCocone (ModuleCat.{u + 1} Λ) c F)) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  rw [Scheme.uliftPointSmallEtale,
    NatIso.isIso_map_iff ((Scheme.pointSmallEtale (c.pt.algClosurePoint s)).uliftSheafFiberIso _)]
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{u, u, u + 1}
  have : PreservesColimitsOfShape Iᵒᵖ
      ((Scheme.pointSmallEtale (c.pt.algClosurePoint s)).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    ((Scheme.pointSmallEtale (c.pt.algClosurePoint s)).skyscraperSheafAdjunction
      (A := ModuleCat.{u + 1} Λ)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let P := isColimitOfPreserves (Scheme.pointSmallEtale (c.pt.algClosurePoint s)).sheafFiber
    (colimit.isColimit (descentDiagram (ModuleCat.{u + 1} Λ) c F))
  let Q := isColimitSheafFiberMapCoconeDescentCocone hc F (c.pt.algClosurePoint s)
  have e : (Scheme.pointSmallEtale (c.pt.algClosurePoint s)).sheafFiber.map
      (colimit.desc _ (descentCocone (ModuleCat.{u + 1} Λ) c F)) =
      (P.coconePointUniqueUpToIso Q).hom :=
    P.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      simp [← Functor.map_comp]
  rw [e]
  infer_instance

/-- The counits `pᵢ^* pᵢ_* F ⟶ F` exhibit `F` as the colimit of the sheaves `pᵢ^* pᵢ_* F`
(blueprint `corollary-open-direct-image-over-field--2`, see
`AlgebraicGeometry.Etale.isIso_colimitDesc_descentCocone`). -/
noncomputable def isColimitDescentCocone :
    IsColimit (descentCocone (ModuleCat.{u + 1} Λ) c F) :=
  have : IsIso ((colimit.isColimit (descentDiagram _ c F)).desc (descentCocone _ c F)) :=
    isIso_colimitDesc_descentCocone hc F
  IsColimit.ofPointIso (colimit.isColimit _)

end AlgebraicGeometry.Etale
