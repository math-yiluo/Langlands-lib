/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLocal -- shake: keep
public import WeilConjectures.TraceFormula.ContractingClosedPiece
public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.FixedLocusExchange

/-!

# The compact-support exchange of the fixed square on pushforwards from the fixed locus

In the fixed square `ι ≫ c = d ≫ Δ` (`ι : F ⟶ C`, `Δ : X ⟶ X ⨯ X` closed immersions), the
compact-support base change `BC : LΔ^* Rc_! ≅ Rd_! Lι^*` (`FixedLocus.lowerShriekBaseChangeIso`)
on the pushforwards `Rι_* M` is described through the composition isomorphism
`Ξ : Rc_! Rι_* ≅ RΔ_* Rd_!` (`lowerStarLowerShriekCompIso`) and the counits:
```
LΔ^* Rc_! Rι_* M --BC--> Rd_! Lι^* Rι_* M --ε_ι--> Rd_! M
  =  LΔ^* Rc_! Rι_* M --Ξ--> LΔ^* RΔ_* Rd_! M --ε_Δ--> Rd_! M
```
(`ProEtale.CondensedRing.Correspondence.FixedLocus.lowerShriekBaseChangeIso_hom_app_comp_counit`,
from the abstract `CategoryTheory.baseChange_app_comp_map_counit`). This is the open/closed
exchange coherence needed to evaluate the compact-support exchange `ν_d` of the fixed square
(`fixedSquareCompactSupportExchange`) at `M = Rj_! ℚ̄_ℓ`: with the diagonal step
(`CategoryTheory.map_comp_mateEquiv_symm_app_comp_counit_comp`),
```
ν_d(M) ≫ g = BC'⁻¹ ≫ LΔ'^*(ν_c(Rι_* M) ≫ t) ≫ ε_{Δ'}
```
whenever `t = Ψ_{X×X}(Ξ(M)) ≫ χ_Δ(Rd_! M) ≫ RΔ'_*(g)`
(`CategoryTheory.fixedSquareCompactSupportExchange_app_comp_eq` and its instance
`ProEtale.CondensedRing.Correspondence.TraceSpecialization.fixedSquareExchange_app_comp_eq`).

Applying the same coherence to the special fixed square `F'` removes `BC'⁻¹`: if the *support
identity* `ν_c(Rι_* M) ≫ Ψ_{X×X}(Ξ(M)) ≫ χ_Δ(Rd_! M) ≫ RΔ'_*(g) = Rc'_!(u) ≫ Ξ'(M') ≫ RΔ'_*(g')`
holds for some `u : Ψ_C Rι_* M ⟶ Rι'_* M'`, then `ν_d(M) ≫ g = Rd'_!(Lι'^*(u) ≫ ε_{ι'}) ≫ g'`
(`CategoryTheory.fixedSquareCompactSupportExchange_app_comp_eq_of_eq`,
`TraceSpecialization.fixedSquareExchange_app_comp_eq_of_eq`). Combined with `ν_X` on an object `T`
receiving `Rd_! M` (`TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_map`),
this computes the exchange `ν_F` of the fixed loci on `M` from the support identity and an
identity `ν_X(T) ≫ w = Ra_{X'!}(χ) ≫ v`
(`TraceSpecialization.fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq`): this is the
form of fact (II) of `ComponentClassReduction` for `M = Rj_! ℚ̄_ℓ`, `T = R(dj)_* ℚ̄_ℓ`, `χ` the
pushforward exchange of `𝒟_B ⟶ 𝒳` and `u` built from that of `𝒟_B ⟶ 𝒞`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section Abstract

variable {DC DF DX DP : Type*} [Category DC] [Category DF] [Category DX] [Category DP]
  {ιU : DC ⥤ DF} {ιS : DF ⥤ DC} {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP} (adjι : ιU ⊣ ιS)
  (adjΔ : ΔU ⊣ ΔS) {cL : DC ⥤ DP} {dL : DF ⥤ DX} (Ξ : ιS ⋙ cL ≅ dL ⋙ ΔS)

/-- **Base change on pushforwards along a closed immersion**: if `BC : Δ^* c_! ⟶ d_! ι^*` is
`Δ^* c_!(η_ι) ≫ Δ^*(Ξ) ≫ ε_Δ` (the form of the compact-support base change for proper
horizontal maps), then on `ι_* M`, `BC` followed by `d_!(ε_ι)` is `Δ^*(Ξ(M)) ≫ ε_Δ`. -/
lemma baseChange_app_comp_map_counit (BC : cL ⋙ ΔU ⟶ ιU ⋙ dL)
    (hBC : ∀ N, BC.app N = ΔU.map (cL.map (adjι.unit.app N)) ≫
      ΔU.map (Ξ.hom.app (ιU.obj N)) ≫ adjΔ.counit.app (dL.obj (ιU.obj N))) (M : DF) :
    BC.app (ιS.obj M) ≫ dL.map (adjι.counit.app M) =
      ΔU.map (Ξ.hom.app M) ≫ adjΔ.counit.app (dL.obj M) := by
  have h₁ := adjΔ.counit.naturality (dL.map (adjι.counit.app M))
  have h₂ := Ξ.hom.naturality (adjι.counit.app M)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at h₁ h₂
  rw [hBC, Category.assoc, Category.assoc, ← h₁]
  simp only [← ΔU.map_comp_assoc]
  rw [← h₂, ← cL.map_comp_assoc, adjι.right_triangle_components]
  simp

end Abstract

section FixedSquare

variable {DC DF DX DP DC' DF' DX' DP' : Type*} [Category DC] [Category DF] [Category DX]
  [Category DP] [Category DC'] [Category DF'] [Category DX'] [Category DP']
  {cL : DC ⥤ DP} {dL : DF ⥤ DX} {ιU : DC ⥤ DF} {ιS : DF ⥤ DC} {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP}
  {cL' : DC' ⥤ DP'} {dL' : DF' ⥤ DX'} {ιU' : DC' ⥤ DF'} {ΔU' : DP' ⥤ DX'} {ΔS' : DX' ⥤ DP'}
  (adjι : ιU ⊣ ιS) (adjΔ : ΔU ⊣ ΔS) (adjΔ' : ΔU' ⊣ ΔS')
  (BC : cL ⋙ ΔU ≅ ιU ⋙ dL) (BC' : cL' ⋙ ΔU' ≅ ιU' ⋙ dL')
  {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
  (νc : ΨC ⋙ cL' ⟶ cL ⋙ ΨP) (χΔ : ΔS ⋙ ΨP ⟶ ΨX ⋙ ΔS') (Ξ : ιS ⋙ cL ≅ dL ⋙ ΔS)

/-- **The exchange of the fixed square on pushforwards**: if the base change `BC` has the form of
`baseChange_app_comp_map_counit` for the composition isomorphism `Ξ : c_! ι_* ≅ Δ_* d_!`, then
for `t = Ψ_P(Ξ(M)) ≫ χ_Δ(d_! M) ≫ Δ'_*(g)`, the exchange `ν_d` of the fixed square
(`fixedSquareCompactSupportExchange`, with `α_Δ` the mate of `χ_Δ`) satisfies
`ν_d(M) ≫ g = BC'⁻¹ ≫ Δ'^*(ν_c(ι_* M) ≫ t) ≫ ε_{Δ'}`. -/
lemma fixedSquareCompactSupportExchange_app_comp_eq
    (hBC : ∀ N, BC.hom.app N = ΔU.map (cL.map (adjι.unit.app N)) ≫
      ΔU.map (Ξ.hom.app (ιU.obj N)) ≫ adjΔ.counit.app (dL.obj (ιU.obj N)))
    (M : DF) {G' : DX'} (g : ΨX.obj (dL.obj M) ⟶ G') (t : ΨP.obj (cL.obj (ιS.obj M)) ⟶ ΔS'.obj G')
    (ht : t = ΨP.map (Ξ.hom.app M) ≫ χΔ.app (dL.obj M) ≫ ΔS'.map g) :
    (fixedSquareCompactSupportExchange adjι BC BC' νc
        ((mateEquiv adjΔ adjΔ').symm χΔ)).app M ≫ g =
      BC'.inv.app (ΨC.obj (ιS.obj M)) ≫ ΔU'.map (νc.app (ιS.obj M) ≫ t) ≫
        adjΔ'.counit.app G' := by
  have hB := baseChange_app_comp_map_counit adjι adjΔ Ξ BC.hom hBC M
  have hD := map_comp_mateEquiv_symm_app_comp_counit_comp adjΔ adjΔ' χΔ (Ξ.hom.app M) g t ht
  have hα := ((mateEquiv adjΔ adjΔ').symm χΔ).naturality (Ξ.hom.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at hα
  simp only [fixedSquareCompactSupportExchange_app, Category.assoc, ← ΨX.map_comp]
  have hα' : ((mateEquiv adjΔ adjΔ').symm χΔ).app (cL.obj (ιS.obj M)) ≫
      ΨX.map (ΔU.map (Ξ.hom.app M)) ≫ ΨX.map (adjΔ.counit.app (dL.obj M)) ≫ g =
      ΔU'.map t ≫ adjΔ'.counit.app G' := by
    rw [← hD, ← reassoc_of% hα]
  rw [hB, ΨX.map_comp, Category.assoc, hα', ΔU'.map_comp, Category.assoc]

variable {ιS' : DF' ⥤ DC'} (adjι' : ιU' ⊣ ιS') (Ξ' : ιS' ⋙ cL' ≅ dL' ⋙ ΔS')

/-- **The inverse base change on pushforwards**: for `BC'` of the form of
`baseChange_app_comp_map_counit` and `u : A ⟶ ι'_* M'`,
`BC'⁻¹(A) ≫ Δ'^*(c'_!(u) ≫ Ξ'(M') ≫ Δ'_*(g')) ≫ ε_{Δ'} = d'_!(ι'^*(u) ≫ ε_{ι'}) ≫ g'`. -/
lemma baseChange_inv_app_comp_map_comp_counit
    (hBC' : ∀ N, BC'.hom.app N = ΔU'.map (cL'.map (adjι'.unit.app N)) ≫
      ΔU'.map (Ξ'.hom.app (ιU'.obj N)) ≫ adjΔ'.counit.app (dL'.obj (ιU'.obj N)))
    {A : DC'} {M' : DF'} (u : A ⟶ ιS'.obj M') {G' : DX'} (g' : dL'.obj M' ⟶ G') :
    BC'.inv.app A ≫ ΔU'.map (cL'.map u ≫ Ξ'.hom.app M' ≫ ΔS'.map g') ≫ adjΔ'.counit.app G' =
      dL'.map (ιU'.map u ≫ adjι'.counit.app M') ≫ g' := by
  have hB := baseChange_app_comp_map_counit adjι' adjΔ' Ξ' BC'.hom hBC' M'
  have hε := adjΔ'.counit.naturality g'
  have hn := BC'.hom.naturality u
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at hε hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hε, ← reassoc_of% hB, reassoc_of% hn, Iso.inv_hom_id_app_assoc]

/-- **The exchange of the fixed square on pushforwards, both sides**: if
`ν_c(ι_* M) ≫ Ψ_P(Ξ(M)) ≫ χ_Δ(d_! M) ≫ Δ'_*(g) = c'_!(u) ≫ Ξ'(M') ≫ Δ'_*(g')` for some
`u : Ψ_C ι_* M ⟶ ι'_* M'`, then `ν_d(M) ≫ g = d'_!(ι'^*(u) ≫ ε_{ι'}) ≫ g'`. -/
lemma fixedSquareCompactSupportExchange_app_comp_eq_of_eq
    (hBC : ∀ N, BC.hom.app N = ΔU.map (cL.map (adjι.unit.app N)) ≫
      ΔU.map (Ξ.hom.app (ιU.obj N)) ≫ adjΔ.counit.app (dL.obj (ιU.obj N)))
    (hBC' : ∀ N, BC'.hom.app N = ΔU'.map (cL'.map (adjι'.unit.app N)) ≫
      ΔU'.map (Ξ'.hom.app (ιU'.obj N)) ≫ adjΔ'.counit.app (dL'.obj (ιU'.obj N)))
    (M : DF) {M' : DF'} (u : ΨC.obj (ιS.obj M) ⟶ ιS'.obj M') {G' : DX'}
    (g : ΨX.obj (dL.obj M) ⟶ G') (g' : dL'.obj M' ⟶ G')
    (h : νc.app (ιS.obj M) ≫ ΨP.map (Ξ.hom.app M) ≫ χΔ.app (dL.obj M) ≫ ΔS'.map g =
      cL'.map u ≫ Ξ'.hom.app M' ≫ ΔS'.map g') :
    (fixedSquareCompactSupportExchange adjι BC BC' νc
        ((mateEquiv adjΔ adjΔ').symm χΔ)).app M ≫ g =
      dL'.map (ιU'.map u ≫ adjι'.counit.app M') ≫ g' := by
  rw [fixedSquareCompactSupportExchange_app_comp_eq adjι adjΔ adjΔ' BC BC' νc χΔ Ξ hBC M g _ rfl,
    h]
  exact baseChange_inv_app_comp_map_comp_counit adjΔ' BC' adjι' Ξ' hBC' u g'

end FixedSquare

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section CompExchange

variable {𝒜 𝒜' ℬ ℬ' 𝒮 𝒮' : Type*} [Category 𝒜] [Category 𝒜'] [Category ℬ] [Category ℬ']
  [Category 𝒮] [Category 𝒮']

/-- The composite exchange `compExchange e e' ν_d ν_a` at `M`, followed by `K(e(M) ≫ a(κ))` for
`κ : d M ⟶ T`, is `e' ≫ a'(ν_d(M) ≫ H(κ)) ≫ ν_a(T)`. -/
lemma compExchange_app_comp_map {G : 𝒜 ⥤ 𝒜'} {H : ℬ ⥤ ℬ'} {K : 𝒮 ⥤ 𝒮'} {d : 𝒜 ⥤ ℬ}
    {d' : 𝒜' ⥤ ℬ'} {a : ℬ ⥤ 𝒮} {a' : ℬ' ⥤ 𝒮'} {f : 𝒜 ⥤ 𝒮} {f' : 𝒜' ⥤ 𝒮'} (e : f ≅ d ⋙ a)
    (e' : f' ≅ d' ⋙ a') (νd : G ⋙ d' ⟶ d ⋙ H) (νa : H ⋙ a' ⟶ a ⋙ K) (M : 𝒜) {T : ℬ}
    (κ : d.obj M ⟶ T) :
    (compExchange e e' νd νa).app M ≫ K.map (e.hom.app M ≫ a.map κ) =
      e'.hom.app (G.obj M) ≫ a'.map (νd.app M ≫ H.map κ) ≫ νa.app T := by
  have hn := νa.naturality κ
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [compExchange_app, Category.assoc]
  rw [← K.map_comp, Iso.inv_hom_id_app_assoc, ← hn, a'.map_comp, Category.assoc]

/-- The algebra of `compExchange_app_comp_map`, for explicit morphisms. -/
lemma comp_map_comp_app_comp_map_eq {H : ℬ ⥤ ℬ'} {K : 𝒮 ⥤ 𝒮'} {a : ℬ ⥤ 𝒮} {a' : ℬ' ⥤ 𝒮'}
    {A : 𝒮'} {B' : ℬ'} {D T : ℬ} {Y : 𝒮} (ε' : A ⟶ a'.obj B') (x : B' ⟶ H.obj D)
    (νa : H ⋙ a' ⟶ a ⋙ K) (ei : a.obj D ⟶ Y) (eh : Y ⟶ a.obj D) (κ : D ⟶ T)
    (he : ei ≫ eh = 𝟙 _) :
    (ε' ≫ a'.map x ≫ νa.app D ≫ K.map ei) ≫ K.map (eh ≫ a.map κ) =
      ε' ≫ a'.map (x ≫ H.map κ) ≫ νa.app T := by
  have hn := νa.naturality κ
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← K.map_comp, reassoc_of% he, ← hn, a'.map_comp, Category.assoc]

/-- The algebra of `fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq`. -/
lemma comp_comp_eq_of_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {a' : 𝒞 ⥤ 𝒟}
    {A B C W : 𝒟} {P Q R G D' : 𝒞} {ν : A ⟶ B} {p : B ⟶ C} {w : C ⟶ W} {e' : A ⟶ a'.obj P}
    {x : P ⟶ Q} {κ : Q ⟶ R} {n : a'.obj R ⟶ C} {χ : R ⟶ G} {v : a'.obj G ⟶ W} {z : P ⟶ D'}
    {g' : D' ⟶ G} (h₁ : ν ≫ p = e' ≫ a'.map (x ≫ κ) ≫ n) (hX : n ≫ w = a'.map χ ≫ v)
    (h₂ : x ≫ κ ≫ χ = z ≫ g') :
    ν ≫ p ≫ w = e' ≫ a'.map (z ≫ g') ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, hX, ← Functor.map_comp_assoc,
    Category.assoc, h₂]

end CompExchange

namespace Correspondence.FixedLocus

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K} (F : c.FixedLocus)

/-- **The base change of the fixed square through the units and counits**: `BC(N)` is
`LΔ^* Rc_! N --η_ι--> LΔ^* Rc_! Rι_* Lι^* N --Ξ--> LΔ^* RΔ_* Rd_! Lι^* N --ε_Δ--> Rd_! Lι^* N`. -/
theorem lowerShriekBaseChangeIso_hom_app_eq
    (N : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    F.lowerShriekBaseChangeIso.hom.app N =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X)).map
          ((boundedConstructibleLowerShriek ℓ c.support).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).unit.app N)) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X)).map
          ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι).obj N)) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).counit.app
          ((boundedConstructibleLowerShriek ℓ F.d).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι).obj N)) := by
  exact boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_eq ℓ F.isPullback F.isPullback.w N

/-- **The base change of the fixed square on pushforwards from the fixed locus**: on `Rι_* M`,
`BC` followed by `Rd_!(ε_ι)` is `LΔ^*(Ξ(M))` followed by the counit of `LΔ^* ⊣ RΔ_*`, for the
composition isomorphism `Ξ : Rc_! Rι_* ≅ RΔ_* Rd_!` (`lowerStarLowerShriekCompIso`). -/
theorem lowerShriekBaseChangeIso_hom_app_comp_counit
    (M : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    F.lowerShriekBaseChangeIso.hom.app ((boundedConstructibleLowerStar ℓ F.ι).obj M) ≫
        (boundedConstructibleLowerShriek ℓ F.d).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).counit.app M) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X)).map
          ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app M) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).counit.app
          ((boundedConstructibleLowerShriek ℓ F.d).obj M) := by
  have h := baseChange_app_comp_map_counit (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (lowerStarLowerShriekCompIso ℓ F.isPullback.w) F.lowerShriekBaseChangeIso.hom
    F.lowerShriekBaseChangeIso_hom_app_eq M
  exact h

end Correspondence.FixedLocus

namespace Correspondence.TraceSpecialization

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
    boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)

/-- **The compact-support exchange of the fixed square on pushforwards from the fixed locus**:
for `M` on `F` and `t = Ψ_{X×X}(Ξ(M)) ≫ χ_Δ(Rd_! M) ≫ RΔ'_*(g)` (`Ξ : Rc_! Rι_* ≅ RΔ_* Rd_!`),
the exchange `ν_d = fixedSquareCompactSupportExchange` of `fixedLocusCompactSupportExchange_eq`
satisfies `ν_d(M) ≫ g = BC'⁻¹ ≫ LΔ'^*(ν_c(Rι_* M) ≫ t) ≫ ε_{Δ'}`. -/
theorem fixedSquareExchange_app_comp_eq (M : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {G' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : ΨX.obj ((boundedConstructibleLowerShriek ℓ F.d).obj M) ⟶ G')
    (t : ΨXX.obj ((boundedConstructibleLowerShriek ℓ c.support).obj
        ((boundedConstructibleLowerStar ℓ F.ι).obj M)) ⟶
      (boundedConstructibleLowerStar ℓ (diag X')).obj G')
    (ht : t = ΨXX.map ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app M) ≫
      χΔ.app ((boundedConstructibleLowerShriek ℓ F.d).obj M) ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map g) :
    (fixedSquareCompactSupportExchange (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
        F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc
        ((CategoryTheory.mateEquiv
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))).symm χΔ)).app M ≫ g =
      F'.lowerShriekBaseChangeIso.inv.app (ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj M)) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X')).map
          (νc.app ((boundedConstructibleLowerStar ℓ F.ι).obj M) ≫ t) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X')).counit.app G' := by
  have h := fixedSquareCompactSupportExchange_app_comp_eq
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))
    F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc χΔ
    (lowerStarLowerShriekCompIso ℓ F.isPullback.w) F.lowerShriekBaseChangeIso_hom_app_eq M g t ht
  exact h

-- elaborating the base change identity of `F'` against the expected hypothesis is slow
/-- **The exchange of the fixed square on pushforwards from the fixed locus, both sides**: if
`ν_c(Rι_* M) ≫ Ψ_{X×X}(Ξ(M)) ≫ χ_Δ(Rd_! M) ≫ RΔ'_*(g) = Rc'_!(u) ≫ Ξ'(M') ≫ RΔ'_*(g')` for
`u : Ψ_C Rι_* M ⟶ Rι'_* M'` (`Ξ, Ξ'` the composition isomorphisms of the fixed squares), then
`ν_d(M) ≫ g = Rd'_!(Lι'^*(u) ≫ ε_{ι'}) ≫ g'`. -/
theorem fixedSquareExchange_app_comp_eq_of_eq (M : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {M' : Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (u : ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj M) ⟶
      (boundedConstructibleLowerStar ℓ F'.ι).obj M')
    {G' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : ΨX.obj ((boundedConstructibleLowerShriek ℓ F.d).obj M) ⟶ G')
    (g' : (boundedConstructibleLowerShriek ℓ F'.d).obj M' ⟶ G')
    (h : νc.app ((boundedConstructibleLowerStar ℓ F.ι).obj M) ≫
        ΨXX.map ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app M) ≫
        χΔ.app ((boundedConstructibleLowerShriek ℓ F.d).obj M) ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map g =
      (boundedConstructibleLowerShriek ℓ c'.support).map u ≫
        (lowerStarLowerShriekCompIso ℓ F'.isPullback.w).hom.app M' ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map g') :
    (fixedSquareCompactSupportExchange (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
        F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc
        ((CategoryTheory.mateEquiv
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))).symm χΔ)).app M ≫ g =
      (boundedConstructibleLowerShriek ℓ F'.d).map
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map u ≫
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).counit.app M') ≫ g' := by
  have h' := fixedSquareCompactSupportExchange_app_comp_eq_of_eq
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))
    F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc χΔ
    (lowerStarLowerShriekCompIso ℓ F.isPullback.w)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι)
    (lowerStarLowerShriekCompIso ℓ F'.isPullback.w) F.lowerShriekBaseChangeIso_hom_app_eq
    ?_ M u g g' ?_
  · exact h'
  · exact F'.lowerShriekBaseChangeIso_hom_app_eq
  · exact h

/-- **`ν_F` through `ν_X`**: for `κ : Rd_! N ⟶ T`, the compact-support exchange `ν_F` of the fixed
loci (`fixedLocusToPointCompactSupportExchange`), followed by `Ψ_pt` of
`Ra_{F!} N ≅ Ra_{X!} Rd_! N ⟶ Ra_{X!} T`, is `Ra_{F'!} ≅ Ra_{X'!} Rd'_!`, then `Ra_{X'!}` of
`ν_d(N) ≫ Ψ_X(κ)` and `ν_X(T)`. -/
theorem fixedLocusToPointCompactSupportExchange_app_comp_map
    {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (N : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (κ : (boundedConstructibleLowerShriek ℓ F.d).obj N ⟶ T) :
    (fixedLocusToPointCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ
        (exceptionalExchange ℓ c.support c'.support νc) νX).app N ≫
      Ψpt.map ((lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d)).hom.app N ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map κ) =
      (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((fixedSquareCompactSupportExchange
            (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
            F.lowerShriekBaseChangeIso F'.lowerShriekBaseChangeIso νc
            ((CategoryTheory.mateEquiv
              (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
              (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X'))).symm χΔ)).app
            N ≫ ΨX.map κ) ≫ νX.app T := by
  rw [fixedLocusToPointCompactSupportExchange_app]
  exact comp_map_comp_app_comp_map_eq _ _ νX _ _ κ (Iso.inv_hom_id_app _ _)

-- unifying the hypotheses with the hand-written statement is slow
/-- **`ν_F` on pushforwards from the fixed locus**: let `κ : Rd_! N ⟶ T`, `χ : Ψ_X T ⟶ G'`,
`u : Ψ_C Rι_* N ⟶ Rι'_* M'` and `g' : Rd'_! M' ⟶ G'` satisfy the support identity
`ν_c(Rι_* N) ≫ Ψ_{X×X}(Ξ(N)) ≫ χ_Δ(Rd_! N) ≫ RΔ'_*(Ψ_X(κ) ≫ χ) = Rc'_!(u) ≫ Ξ'(M') ≫ RΔ'_*(g')`,
and let `ν_X(T) ≫ w = Ra_{X'!}(χ) ≫ v` (the exchange `ν_X` on `T`). Then `ν_F(N)` followed by
`Ψ_pt(Ra_{F!} N ≅ Ra_{X!} Rd_! N ⟶ Ra_{X!} T) ≫ w` is
`(Ra_{F'!} ≅ Ra_{X'!} Rd'_!) ≫ Ra_{X'!}(Rd'_!(Lι'^*(u) ≫ ε_{ι'}) ≫ g') ≫ v`. -/
theorem fixedLocusToPointCompactSupportExchange_app_comp_eq_of_eq
    {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (N : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {M' : Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (u : ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj N) ⟶
      (boundedConstructibleLowerStar ℓ F'.ι).obj M')
    {T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (κ : (boundedConstructibleLowerShriek ℓ F.d).obj N ⟶ T)
    {G' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (χ : ΨX.obj T ⟶ G')
    (g' : (boundedConstructibleLowerShriek ℓ F'.d).obj M' ⟶ G')
    (h : νc.app ((boundedConstructibleLowerStar ℓ F.ι).obj N) ≫
        ΨXX.map ((lowerStarLowerShriekCompIso ℓ F.isPullback.w).hom.app N) ≫
        χΔ.app ((boundedConstructibleLowerShriek ℓ F.d).obj N) ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map (ΨX.map κ ≫ χ) =
      (boundedConstructibleLowerShriek ℓ c'.support).map u ≫
        (lowerStarLowerShriekCompIso ℓ F'.isPullback.w).hom.app M' ≫
        (boundedConstructibleLowerStar ℓ (diag X')).map g')
    {W : Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (w : Ψpt.obj ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj T) ⟶ W)
    (v : (boundedConstructibleLowerShriek ℓ (toPoint X')).obj G' ⟶ W)
    (hX : νX.app T ≫ w = (boundedConstructibleLowerShriek ℓ (toPoint X')).map χ ≫ v) :
    (fixedLocusToPointCompactSupportExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ
        (exceptionalExchange ℓ c.support c'.support νc) νX).app N ≫
      Ψpt.map ((lowerShriekCompOfEq ℓ F.d (toPoint X) (comp_toPoint F.d)).hom.app N ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map κ) ≫ w =
      (lowerShriekCompOfEq ℓ F'.d (toPoint X') (comp_toPoint F'.d)).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((boundedConstructibleLowerShriek ℓ F'.d).map
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map u ≫
              (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).counit.app M') ≫ g') ≫
        v := by
  exact comp_comp_eq_of_eq (a' := boundedConstructibleLowerShriek ℓ (toPoint X'))
    (fixedLocusToPointCompactSupportExchange_app_comp_map (F := F) (F' := F') ΨC ΨX ΨXX χΔ νc
      νX N κ) hX
    (fixedSquareExchange_app_comp_eq_of_eq (F := F) (F' := F') ΨC ΨX ΨXX χΔ νc N u
      (ΨX.map κ ≫ χ) g' h)

end Correspondence.TraceSpecialization

end AlgebraicGeometry.ProEtale.CondensedRing
