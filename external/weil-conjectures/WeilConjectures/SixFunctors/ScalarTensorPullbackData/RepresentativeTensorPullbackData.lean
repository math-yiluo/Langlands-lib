/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.Tensor.RepresentativeTensorCube
public import WeilConjectures.SixFunctors.Supporting.Tensor.RepresentativeTensorOrdinaryPullbackLaw

/-! # Explicit pullback data for a representative tensor cube

Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-representative-tensor-pullback-data).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures

variable {K H K' H' D E D' E' : Type*}
  [Category K] [Category H] [Category K'] [Category H']
  [Category D] [Category E] [Category D'] [Category E']

/-- The actual pullback functors and comparison maps, before their four laws.
Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-representative-tensor-pullback-data). -/
structure ScalarTensorPullbackData
    (Y : ScalarTensorRepresentativeData K K' D D')
    (X : ScalarTensorRepresentativeData H H' E E')
    extends TensorFixedPullbackData Y.toTensorFixedRepresentativeData
      X.toTensorFixedRepresentativeData where
  B : K' ⥤ H'
  G : D' ⥤ E'
  g : Y.q' ⋙ G ≅ B ⋙ X.q'
  c : Y.U ⋙ B ≅ A ⋙ X.U
  alpha : Y.E ⋙ G ≅ F ⋙ X.E
  hB : ∀ P, Y.P' P → X.P' (B.obj P)
  mG : Y.t' ⋙ B ⟶ (B.prod B) ⋙ X.t'
  phiG : Y.T' ⋙ G ⟶ (G.prod G) ⋙ X.T'

namespace ScalarTensorPullbackData
variable {Y : ScalarTensorRepresentativeData K K' D D'}
  {X : ScalarTensorRepresentativeData H H' E E'}

/-- The fixed-coefficient representative law.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-pullback-data). -/
def fixedLaw (S : ScalarTensorPullbackData Y X) : Prop :=
  S.toTensorFixedPullbackData.law

/-- The intrinsic representative law.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-pullback-data). -/
def intrinsicLaw (S : ScalarTensorPullbackData Y X) : Prop :=
  ∀ (P Q : K') (hp : Y.P' P) (hq : Y.P' Q),
    S.G.map (Y.r'.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ S.phiG.app (Y.q'.obj P, Y.q'.obj Q) ≫
        X.T'.map (Prod.mkHom (S.g.hom.app P) (S.g.hom.app Q)) =
      S.g.hom.app (Y.t'.obj (P, Q)) ≫ X.q'.map (S.mG.app (P, Q)) ≫
        X.r'.hom.app (⟨S.B.obj P, S.hB P hp⟩, ⟨S.B.obj Q, S.hB Q hq⟩)

/-- The unary inverse-mate factor law.
Source: Stacks Tag 07A6 (blueprint: def-sf-representative-tensor-pullback-data). -/
def factorsLaw (S : ScalarTensorPullbackData Y X) : Prop :=
  ∀ P : K,
    X.E.map (S.f.hom.app P) ≫ X.e.hom.app (S.A.obj P) ≫ X.q'.map (S.c.inv.app P) =
      S.alpha.inv.app (Y.q.obj P) ≫ S.G.map (Y.e.hom.app P) ≫ S.g.hom.app (Y.U.obj P)

/-- The ordinary chain tensor law.
Source: Stacks Tag 07A4 (blueprint: def-sf-representative-tensor-pullback-data). -/
def chainLaw (S : ScalarTensorPullbackData Y X) : Prop :=
  tensorOrdinaryPullbackLaw Y.t X.t Y.t' X.t' Y.U X.U S.A S.B S.c
    S.mF Y.b X.b S.mG

/-- Apply the proved categorical cube to the four laws of specified pullback data.
Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-representative-tensor-pullback-data).

Proof: supply the stored functors and maps and the four stated laws to
finiteScalarRepresentativeTensorCube. No data are chosen or modified. -/
theorem tensorSquare (S : ScalarTensorPullbackData Y X)
    (hf : S.fixedLaw) (hg : S.intrinsicLaw) (hc : S.factorsLaw) (ht : S.chainLaw)
    (P Q : K) (hp : Y.P P) (hq : Y.P Q) :
    X.E.map ((S.phiF.app (Y.q.obj P)).app (Y.q.obj Q)) ≫
        (X.tau.hom.app (S.F.obj (Y.q.obj P))).app (S.F.obj (Y.q.obj Q)) =
      S.alpha.inv.app ((Y.T.obj (Y.q.obj P)).obj (Y.q.obj Q)) ≫
        S.G.map ((Y.tau.hom.app (Y.q.obj P)).app (Y.q.obj Q)) ≫
        ((curry.map S.phiG ≫ (curryObjProdComp S.G S.G X.T').hom).app
          (Y.E.obj (Y.q.obj P))).app (Y.E.obj (Y.q.obj Q)) ≫
        ((curry.obj X.T').map (S.alpha.hom.app (Y.q.obj P))).app _ ≫
        ((curry.obj X.T').obj _).map (S.alpha.hom.app (Y.q.obj Q)) := by
  exact finiteScalarRepresentativeTensorCube Y X S.A S.B S.F S.G S.f S.g S.c S.alpha
    S.hA S.hB S.mF S.mG S.phiF S.phiG hf hg hc ht P Q hp hq

end ScalarTensorPullbackData
end WeilConjectures
