/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalizationFrobenius

/-!

# The closed-piece Frobenius operator as the Frobenius of a coefficient map

In the setting of `WeilConjectures.TraceFormula.LocalizationFrobenius`, the operator `E_Z` on
`RΓ_c(X, Ri_* Li^* K)` is `RΓ_c(X, ψ_Z) ∘ Φ^♯` for a Frobenius coefficient map
`ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K`, compatible with the unit `K ⟶ Ri_* Li^* K` of the
localization triangle. The abstract shape of the computation is isolated first, for functors
between arbitrary categories.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.closedPieceFrobeniusCoeff`: the coefficient
  map `ψ_Z`.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusClosedPiece_eq`:
  `E_Z = RΓ_c(X, ψ_Z) ∘ Φ^♯`.
- `WeilBoundedConstructible.upperStar_map_unit_comp_closedPieceFrobeniusCoeff`
  (the compatibility of `ψ_Z` with the unit).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section PieceCoefficients

variable {CX CZ D : Type*} [Category CX] [Category CZ] [Category D] {aX : CX ⥤ D}
  {aZ : CZ ⥤ D} {uΦ : CX ⥤ CX} {ui : CX ⥤ CZ} {uΦZ : CZ ⥤ CZ} {ri : CZ ⥤ CX}

/-- The abstract shape of the compatibility of the pullback to the closed piece with the
Frobenius: from the composition laws `p₁ = (i ≫ Φ)^♯` and `p₂ = (Φ_Z ≫ i)^♯` and their
comparison `e`, the square
```
aX M ─────pΦ─────▶ aX (uΦ M)
  │                    │
  pi                   pi
  ▼                    ▼
aZ (ui M) ──pΦZ ≫ aZ cmp──▶ aZ (ui (uΦ M))
```
commutes. -/
lemma closedPiece_pullback_comm_of_comp (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) {u₁ u₂ : CX ⥤ CZ} (p₁ : aX ⟶ u₁ ⋙ aZ) (p₂ : aX ⟶ u₂ ⋙ aZ)
    (c₁ : u₁ ≅ uΦ ⋙ ui) (c₂ : u₂ ≅ ui ⋙ uΦZ) (M : CX) (e : u₂.obj M ⟶ u₁.obj M)
    (h1 : p₁.app M = pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M))
    (h2 : p₂.app M = pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M))
    (h3 : p₂.app M ≫ aZ.map e = p₁.app M) (cmp : uΦZ.obj (ui.obj M) ⟶ ui.obj (uΦ.obj M))
    (hc : cmp = c₂.inv.app M ≫ e ≫ c₁.hom.app M) :
    pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map cmp = pΦ.app M ≫ pi.app (uΦ.obj M) := by
  have h3' : pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (c₂.inv.app M) ≫ aZ.map e =
      pΦ.app M ≫ pi.app (uΦ.obj M) ≫ aZ.map (c₁.inv.app M) := by
    simpa [h1, h2] using h3
  rw [hc, Functor.map_comp, Functor.map_comp, reassoc_of% h3']
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The abstract shape of the closed-piece operator: conjugated along `c : ri ⋙ aX ≅ aZ`, the
operator `pΦZ ≫ aZ g` of a coefficient map `g : uΦZ N ⟶ N` is `pΦ` followed by the image of the
adjoint coefficient map, for pullback maps `pi` given by the unit of `ui ⊣ ri`:
```
aX (ri N) ──c──▶ aZ N ──pΦZ ≫ aZ g──▶ aZ N ──c⁻¹──▶ aX (ri N)
    ‖                                                  ‖
aX (ri N) ──pΦ──▶ aX (uΦ (ri N)) ──aX (closedPieceCoeff g)──▶ aX (ri N)
```
-/
lemma closedPiece_conj_eq_of_unit (adj : ui ⊣ ri) (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (c : ri ⋙ aX ≅ aZ)
    (hpi : ∀ M, pi.app M = aX.map (adj.unit.app M) ≫ c.hom.app (ui.obj M))
    (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui)
    (hcomm : ∀ M, pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (cmp.hom.app M) =
      pΦ.app M ≫ pi.app (uΦ.obj M)) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    c.hom.app N ≫ (pΦZ.app N ≫ aZ.map g) ≫ c.inv.app N =
      pΦ.app (ri.obj N) ≫ aX.map (adj.unit.app _ ≫ ri.map (cmp.inv.app (ri.obj N) ≫
        uΦZ.map (adj.counit.app N) ≫ g)) := by
  have hc : c.hom.app N = pi.app (ri.obj N) ≫ aZ.map (adj.counit.app N) := by
    have hn := c.hom.naturality (adj.counit.app N)
    dsimp at hn
    rw [hpi, Category.assoc, ← hn, ← aX.map_comp_assoc, adj.right_triangle_components]
    simp
  have h' : pi.app (ri.obj N) ≫ pΦZ.app (ui.obj (ri.obj N)) =
      pΦ.app (ri.obj N) ≫ pi.app (uΦ.obj (ri.obj N)) ≫ aZ.map (cmp.inv.app (ri.obj N)) := by
    rw [← reassoc_of% (hcomm (ri.obj N)), ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hnat := c.hom.naturality (cmp.inv.app (ri.obj N) ≫ uΦZ.map (adj.counit.app N) ≫ g)
  have hn := pΦZ.naturality (adj.counit.app N)
  dsimp at hnat hn
  simp only [Functor.map_comp, Category.assoc] at hnat
  rw [← cancel_mono (c.hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  rw [hnat, ← Category.assoc (aX.map _), ← hpi, ← reassoc_of% h', reassoc_of% hn.symm,
    ← reassoc_of% hc]

/-- The adjoint coefficient map of the restriction `cmp ≫ ui φ` of a coefficient map `φ` is
compatible with `φ` along the unit of `ui ⊣ ri`:
```
uΦ K ──uΦ η──▶ uΦ (ri (ui K)) ──closedPieceCoeff (cmp ≫ ui φ)──▶ ri (ui K)
  ‖                                                                ‖
uΦ K ─────────────φ─────────────▶ K ────────────η────────────▶ ri (ui K)
```
-/
lemma closedPiece_unit_comp_coeff_eq (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (K : CX)
    (φ : uΦ.obj K ⟶ K) :
    uΦ.map (adj.unit.app K) ≫ adj.unit.app (uΦ.obj (ri.obj (ui.obj K))) ≫
      ri.map (cmp.inv.app (ri.obj (ui.obj K)) ≫
        uΦZ.map (adj.counit.app (ui.obj K)) ≫ cmp.hom.app K ≫ ui.map φ) =
      φ ≫ adj.unit.app K := by
  have hu := adj.unit.naturality (uΦ.map (adj.unit.app K))
  have hu' := adj.unit.naturality φ
  have hc := cmp.inv.naturality (adj.unit.app K)
  dsimp at hu hu' hc
  rw [reassoc_of% hu, ← Functor.map_comp, reassoc_of% hc, ← Functor.map_comp_assoc uΦZ,
    adj.left_triangle_components]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact hu'.symm

/-- The abstract Frobenius coefficient of the closed piece:
`uΦ ri N ⟶ ri ui uΦ ri N ≅ ri uΦZ ui ri N ⟶ ri uΦZ N ⟶ ri N` for a coefficient map
`g : uΦZ N ⟶ N`, through the unit and counit of `ui ⊣ ri` and the comparison `cmp`. -/
def closedPieceCoeff (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    uΦ.obj (ri.obj N) ⟶ ri.obj N :=
  adj.unit.app _ ≫ ri.map (cmp.inv.app (ri.obj N) ≫ uΦZ.map (adj.counit.app N) ≫ g)

/-- `closedPiece_conj_eq_of_unit` for `closedPieceCoeff`. -/
lemma closedPiece_conj_eq_closedPieceCoeff (adj : ui ⊣ ri) (pΦ : aX ⟶ uΦ ⋙ aX) (pi : aX ⟶ ui ⋙ aZ)
    (pΦZ : aZ ⟶ uΦZ ⋙ aZ) (c : ri ⋙ aX ≅ aZ)
    (hpi : ∀ M, pi.app M = aX.map (adj.unit.app M) ≫ c.hom.app (ui.obj M))
    (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui)
    (hcomm : ∀ M, pi.app M ≫ pΦZ.app (ui.obj M) ≫ aZ.map (cmp.hom.app M) =
      pΦ.app M ≫ pi.app (uΦ.obj M)) (N : CZ) (g : uΦZ.obj N ⟶ N) :
    (c.hom.app N : aX.obj (ri.obj N) ⟶ aZ.obj N) ≫ (pΦZ.app N ≫ aZ.map g) ≫
        (c.inv.app N : aZ.obj N ⟶ aX.obj (ri.obj N)) =
      pΦ.app (ri.obj N) ≫ aX.map (closedPieceCoeff adj cmp N g) :=
  closedPiece_conj_eq_of_unit adj pΦ pi pΦZ c hpi cmp hcomm N g

/-- `closedPiece_unit_comp_coeff_eq` for `closedPieceCoeff`. -/
lemma closedPieceCoeff_unit_comm (adj : ui ⊣ ri) (cmp : ui ⋙ uΦZ ≅ uΦ ⋙ ui) (K : CX)
    (φ : uΦ.obj K ⟶ K) :
    uΦ.map (adj.unit.app K) ≫ closedPieceCoeff adj cmp (ui.obj K) (cmp.hom.app K ≫ ui.map φ) =
      φ ≫ adj.unit.app K := by
  rw [closedPieceCoeff]
  exact closedPiece_unit_comp_coeff_eq adj cmp K φ

end PieceCoefficients

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

-- matching the composites of the restricted `ℚ̲̄_ℓ`-pullbacks is expensive
omit [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦZ.left] in
/-- The pullback square of the closed piece on compactly supported cohomology: for
`Φ_Z ≫ i = i ≫ Φ`, `i^♯ ≫ Φ_Z^♯ ≫ RΓ_c(Z, cmp) = Φ^♯ ≫ i^♯`, where
`cmp : LΦ_Z^* Li^* ≅ Li^* LΦ^*` is the pullback comparison of the square. -/
lemma compactPullback_comp_compactPullback_comparison (hi : ΦZ ≫ i = i ≫ Φ)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ i).app M ≫
        (compactPullback ℓ ΦZ).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
          ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app M) =
      (compactPullback ℓ Φ).app M ≫
        (compactPullback ℓ i).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj M) := by
  have : IsProper (i ≫ Φ).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (ΦZ ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  refine closedPiece_pullback_comm_of_comp (compactPullback ℓ Φ) (compactPullback ℓ i)
    (compactPullback ℓ ΦZ) (compactPullback ℓ (i ≫ Φ)) (compactPullback ℓ (ΦZ ≫ i))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i Φ)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ i) M
    (eqToHom (by rw [hi])) ?_ ?_ ?_ _ ?_
  · exact compactPullback_comp_app ℓ i Φ M
  · exact compactPullback_comp_app ℓ ΦZ i M
  · exact compactPullback_app_congr ℓ hi M
  · exact weilUpperStarComparison_hom_app ℓ ΦZ Φ i hi M

variable (ℓ) in
/-- The Frobenius coefficient `ψ_Z : LΦ^* Ri_* Li^* K ⟶ Ri_* Li^* K` of the closed piece: the
adjoint of `Li^* LΦ^* Ri_* Li^* K ≅ LΦ_Z^* Li^* Ri_* Li^* K ⟶ LΦ_Z^* Li^* K ≅ Li^* LΦ^* K ⟶ Li^* K`,
of the pullback comparison, the counit of `Li^* ⊣ Ri_*` and `Li^* φ`. -/
noncomputable def closedPieceFrobeniusCoeff (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
      (boundedConstructibleLowerStar ℓ i).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) :=
  closedPieceCoeff
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) _
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)

-- the closed-piece operator unfolds to a long composite
omit [IsUniversalHomeomorphism Φ.left] [IsUniversalHomeomorphism ΦZ.left] in
/-- The operator `E_Z` of the closed piece is `RΓ_c(X, ψ_Z) ∘ Φ^♯` on `RΓ_c(X, Ri_* Li^* K)`. -/
lemma compactFrobeniusClosedPiece_eq (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) :
    compactFrobeniusClosedPiece ℓ hi K =
      (compactPullback ℓ Φ).app
          ((boundedConstructibleLowerStar ℓ i).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj
              K.carrier)) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          (closedPieceFrobeniusCoeff ℓ hi K) := by
  rw [compactFrobeniusClosedPiece]
  exact closedPiece_conj_eq_closedPieceCoeff
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (compactPullback ℓ Φ) (compactPullback ℓ i) (compactPullback ℓ ΦZ)
    (boundedConstructibleLowerStarCompToPoint ℓ i) (compactPullback_app_eq (ℓ := ℓ) i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) (compactPullback_comp_compactPullback_comparison hi)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)
    ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)

-- the compactly supported Frobenius of the triangle unfolds to long composites
omit [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦZ.left]
  [IsUniversalHomeomorphism ΦZ.left] [IsClosedImmersion i.left] in
/-- The Frobenius coefficient of the closed piece is compatible with the unit
`η : K ⟶ Ri_* Li^* K`. -/
lemma upperStar_map_unit_comp_closedPieceFrobeniusCoeff (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          i).unit.app K.carrier) ≫ closedPieceFrobeniusCoeff ℓ hi K =
      K.str.hom ≫ (boundedConstructibleUpperStarLowerStarAdjunction
        ℓ i).unit.app K.carrier := by
  exact closedPieceCoeff_unit_comm
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i)
    (weilUpperStarComparison ℓ ΦZ Φ i hi) K.carrier K.str.hom

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
