/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import all WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemTransport
import all WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSiteOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProperOpenOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProOriginExactLinear
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalOriginAdjunctionEvaluation

/-! # Exceptional system transport in the fixed integral coordinates
Source: Zheng, Construction 5.25, Lemma 5.22 and Proposition 5.24.
(blueprint: lem-sf-exceptional-integral-system-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary exceptional system construction and its pro-etale transport exist
for the lifted valuation ring used by integral reconstruction.
Source: Zheng, Construction 5.25 and Lemma 5.22; the generic transport argument
of lem-sf-exceptional-system-transport, with the fixed lifted coefficient ring.
(blueprint: lem-sf-exceptional-integral-system-existence).

Proof: the lifted valuation ring is complete, its uniformizer is regular, and its
positive quotients are finite prime-power-torsion rings. Apply the ordinary Brown
construction with those stages. At X, Y and the compactification obtain the actual
site adjunctions, and use the proper and open mates to compare compact support.
On the origin subcategories these comparisons are invertible. Conjugating the
ordinary adjunction along the site adjunctions therefore gives the displayed
system adjunction and its transpose equation. Apply the same argument at each
finite level; the evaluation squares for the original site maps identify their
units, counits and quotient transitions. Retain the exact, additive and linear
structures and the normalizedness and lower bound of the transported right
functor. This is the generic system-transport proof with only the ring coordinates
changed; no absolute separatedness or faithfulness of finite evaluation is used. -/
theorem exceptionalIntegralSystemExistence
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (Systems l E c) := by
  obtain ⟨hcomplete, hregular, hfinite, htorsion⟩ := exceptionalStages l E
  let := hcomplete
  obtain ⟨S, ⟨G⟩⟩ := exceptionalSupportFromStages l D hl f
    (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
    hregular hfinite htorsion c
  let O := integralExceptionalIntegers l E
  let ell := integralExceptionalUniformizer l E
  let (n : ℕ) : Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) := hfinite n
  obtain ⟨CX, hX, heX, huX, hcX, hiX⟩ := exceptionalSiteOriginComparison O ell X S.PX
  obtain ⟨CY, hY, heY, _huY, _hcY, _hiY⟩ := exceptionalSiteOriginComparison O ell Y S.PY
  obtain ⟨CZ, hZ, _heZ, _huZ, _hcZ, _hiZ⟩ :=
    exceptionalSiteOriginComparison O ell c.Z S.PZ
  obtain ⟨P, R, hcomparison, hleft, hfiniteLeft, hfiniteComparison, hfiniteBound,
    hcomparisonEvaluation⟩ := exceptionalProperOpenOriginComparison G CX CY CZ hX hY hZ
  have horigin (M) (hM : CX.origin M) :
      IsIso ((exceptionalSystemOriginComparison R).app M) := by
    obtain ⟨a, ha⟩ := hM.1
    have := hcomparison (CX.image.system.direct.obj M) ⟨a, hX.directBound a M ha⟩
    have := hX.counit M hM
    let e := asIso ((exceptionalSystemComparison R).app
        (CX.image.system.direct.obj M)) ≪≫
      ((Functor.associator CX.image.system.direct CX.image.system.inverse
        (exceptionalProSupport P)).symm.app M) ≪≫
      asIso ((exceptionalProSupport P).map (CX.image.system.adjunction.counit.app M)) ≪≫
      (Functor.leftUnitor (exceptionalProSupport P)).app M
    change IsIso e.hom
    infer_instance
  have hright (N) (hN : CY.origin N) :
      CX.origin ((exceptionalSystemRight G CX CY).obj N) := by
    obtain ⟨a, ha⟩ := hN.1
    obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
    exact hX.inverseOrigin _ ⟨a - d, hd a _ (hY.directBound a N ha)⟩
  let adj := makeOriginAdjunction G.adjunction
    CX.image.system.adjunction CY.image.system.adjunction
    (exceptionalProSupport P) CX.origin CY.origin (exceptionalSystemOriginComparison R)
    hleft hright horigin hX.counit (fun N hN ↦ by
      obtain ⟨a, ha⟩ := hN.1
      obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
      exact hX.unit _ ⟨a - d, hd a _ (hY.directBound a N ha)⟩)
  let finiteAdj (n : ℕ) := makeOriginAdjunction (G.levelAdjunction n)
    (CX.image.level n).adjunction (CY.image.level n).adjunction
    (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct)
    (CX.levelOrigin n) (CY.levelOrigin n) (exceptionalSystemLevelOriginComparison R n)
    (hfiniteLeft n)
    (fun N hN ↦ hiX n _ (hfiniteBound n N hN))
    (hfiniteComparison n) (hcX n)
    (fun N hN ↦ huX n _ (hfiniteBound n N hN))
  obtain ⟨la, ra, ls, rs, sx, sy, hle, hre, hll, hrl⟩ :=
    exceptionalProOriginExactLinear G CX CY CZ P
  let record : ExceptionalSystemTransportData G CX CY CZ P R := {
    siteX := hX
    siteY := hY
    siteZ := hZ
    systemAdjunction := adj
    finiteAdjunction := finiteAdj
    evaluationOriginX := heX
    evaluationOriginY := heY
    leftAdditive := la
    rightAdditive := ra
    leftShift := ls
    rightShift := rs
    scalarX := sx
    scalarY := sy }
  obtain ⟨hunit, hcounit, hquotient⟩ :=
    exceptionalOriginAdjunctionEvaluation G CX CY CZ P R record hcX hcomparisonEvaluation
  let ht : ExceptionalSystemTransport G CX CY CZ P R :=
    ⟨record, hcomparison, horigin, hcomparisonEvaluation, hunit, hcounit, hquotient,
      hle, hre, hll, hrl, exceptionalSystemRight_normalized G CX CY hX hY,
      exceptionalSystemRight_lowerBound G CX CY hX hY⟩
  exact ⟨{
    ordinary := S
    right := G
    siteX := CX
    siteY := CY
    siteZ := CZ
    properOpen := P
    comparison := R
    transport := ht }⟩

end WeilConjectures.ExceptionalIntegralReconstruction
