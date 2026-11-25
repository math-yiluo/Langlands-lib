/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationProperPoint
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnProperShape

/-!

# The exchange `ν_X` on objects pushed forward from a proper scheme

For `ν_X = pointCompactSupportExchangeOfOpenImmersion x u k'` (`u : X ⊂ Y` open, `Y` proper) and a
morphism of models `φ_g : M_B ⟶ 𝒳` over `g : B ⟶ X`, the identity of
`openPointExchangeAux_app_comp_aux_of_eq` on `g_* N`
(`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar`): `ν_X` read through the composition
isomorphisms, followed by the proper exchange of `B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` (`pointCompModelHom`),
is `Rp'_* h'_!(e'_u ∘ u'_!(χ_g))`, given the ambient identity `hC`.

The ingredients of `hC` are proved here: `ν_u` on pushforwards
(`NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app`), the identification of the `ν_h` of
`pointExchangeAux` with `lowerShriekExchangeOfInv` (`pointOpenExchange_app_eq`), and their
composition with `NearbyCyclesModel.Hom.compactSupportExchange_comp_app`
(`map_comp_exchange_aux`). The description of the mate `ν_u` on bounded constructible complexes
is `map_mateEquiv_inv_liftExchange`.

The ambient identity `hC` itself, in the shape of `openPointExchangeAux_app_comp_aux_of_eq`, is
`NearbyCyclesModel.Hom.pointExchange_comp_app` (generic coefficients `Λ`), deduced from its
abstract form `pointExchange_comp_aux`; `NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq` is
the form of it matching the instances syntactically (used in `PointExchangeOnComponentBdc`).

## Implementation notes

The statement is `∀ hC, type_of% (…)`. All identifications of `Rg_* ⋙ 𝟭` with `Rg_*` (from
`h = 𝟙`) are made in `pointExchange_comp_aux`, on abstract categories, where they are cheap; on
derived categories (`Functor.obj` with different source categories) both the elaborator and the
kernel unfold instead of failing fast. The instance arguments of
`NearbyCyclesModel.Hom.pointExchange_comp_app` are implicit, so that they are assigned by
unification with the goal instead of being synthesized.

`apply NearbyCyclesModel.Hom.pointExchange_comp_app` closes the `hC` of
`pointCompactSupportExchangeOfSeparated_app_lowerStar_component` in the elaborator, but the kernel
check runs out of memory: under the projections `Quiver.Hom`/`Prefunctor.obj` (reducibility hint
`abbrev`) the kernel unfolds instead of comparing arguments, so every subterm on which the goal and
the instance of the lemma differ (although each such pair is checked instantly in isolation) is
fatal. How these differences are removed is explained in the notes of
`PointExchangeOnComponentBdc`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- `ν_h` of `pointExchangeAux` is `lowerShriekExchangeOfInv` for the adjunction `𝟭 ⊣ L1`. -/
lemma pointOpenExchange_app_eq {DX DX' DP : Type*} [Category DX] [Category DX'] [Category DP]
    {ΨX : DX ⥤ DX'} {ΨP : DX ⥤ DP} {Dh : DX' ⥤ DP} {Lh : DP ⥤ DX'} {L1 : DX ⥤ DX}
    (adj : Dh ⊣ Lh) (e : 𝟭 DX ≅ L1) (α : ΨP ⋙ Lh ⟶ L1 ⋙ ΨX) [IsIso α] (Z : DX) :
    (pointOpenExchange adj e α).app Z =
      (lowerShriekExchangeOfInv (Adjunction.id.ofNatIsoRight e) adj α).app Z := by
  simp [pointOpenExchange, lowerShriekExchangeOfInv]

/-- Composing the identity `a ≫ b ≫ c = d ≫ e'` (`ν_u` on pushforwards) with the identity `k₂`
(`ν_Y` on pushforwards). -/
lemma map_comp_exchange_aux {C D E : Type*} [Category C] [Category D] [Category E] (Dh : C ⥤ D)
    (Rp : D ⥤ E) {x₀ x₁ x₂ x₃ y : C} {z w : D} {s t : E} {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂}
    {c : x₂ ⟶ x₃} {d : x₀ ⟶ y} {e' : y ⟶ x₃} (k₁ : a ≫ b ≫ c = d ≫ e') {ν₁ ν₂ : Dh.obj x₂ ⟶ z}
    (hν : ν₁ = ν₂) {eH : Dh.obj x₃ ⟶ w} {χ₀ : Rp.obj z ⟶ s} {r : s ⟶ t} {cj : Rp.obj w ⟶ t}
    (k₂ : Rp.map ν₂ ≫ χ₀ ≫ r = Rp.map (Dh.map c ≫ eH) ≫ cj) :
    Rp.map (Dh.map (a ≫ b)) ≫ Rp.map ν₁ ≫ χ₀ ≫ r = Rp.map (Dh.map (d ≫ e') ≫ eH) ≫ cj := by
  subst hν
  rw [k₂, ← Rp.map_comp_assoc, ← Dh.map_comp_assoc, Category.assoc, k₁]

/-- **The ambient identity of `ν_X` on pushforwards**, in abstract categories: the composite of
`ν_u` on pushforwards (`lowerShriekExchangeOfInv_app_comp_aux` for `u`) and of `ν_Y` on
pushforwards (`compactSupportExchange_comp_aux` for `h = 𝟙`, written with `pointOpenExchange`). -/
lemma pointExchange_comp_aux {DB DX DY SB SX SY SP DS SS : Type*} [Category DB] [Category DX]
    [Category DY] [Category SB] [Category SX] [Category SY] [Category SP] [Category DS]
    [Category SS] {Lg : DX ⥤ DB} {Rg : DB ⥤ DX} {Lu : DY ⥤ DX} {Lgu : DY ⥤ DB} {Rgu : DB ⥤ DY}
    {Lg' : SX ⥤ SB} {Rg' : SB ⥤ SX} {Lu' : SY ⥤ SX} {Lgu' : SY ⥤ SB} {Rgu' : SB ⥤ SY}
    (adjg : Lg ⊣ Rg) (adjgu : Lgu ⊣ Rgu) (adjg' : Lg' ⊣ Rg') (adjgu' : Lgu' ⊣ Rgu')
    (cu : Lgu ≅ Lu ⋙ Lg) (cu' : Lgu' ≅ Lu' ⋙ Lg') {ΨB : DB ⥤ SB} {ΨX : DX ⥤ SX} {ΨY : DY ⥤ SY}
    (αg : ΨX ⋙ Lg' ⟶ Lg ⋙ ΨB) (αu : ΨY ⋙ Lu' ⟶ Lu ⋙ ΨX) (αgu : ΨY ⋙ Lgu' ⟶ Lgu ⋙ ΨB)
    (hαu : ∀ K, αgu.app K ≫ ΨB.map (cu.hom.app K) =
      cu'.hom.app (ΨY.obj K) ≫ Lg'.map (αu.app K) ≫ αg.app (Lu.obj K))
    (χg : Rg ⋙ ΨX ⟶ ΨB ⋙ Rg') (hχg : χg = (mateEquiv adjg adjg' αg))
    (χgu : Rgu ⋙ ΨY ⟶ ΨB ⋙ Rgu') (hχgu : χgu = (mateEquiv adjgu adjgu' αgu))
    (bu : Rgu ⋙ Lu ⟶ Rg)
    (hbu : ∀ N, Lg.map (bu.app N) ≫ adjg.counit.app N =
      cu.inv.app (Rgu.obj N) ≫ adjgu.counit.app N)
    (bu' : Rgu' ⋙ Lu' ⟶ Rg')
    (hbu' : ∀ N, Lg'.map (bu'.app N) ≫ adjg'.counit.app N =
      cu'.inv.app (Rgu'.obj N) ≫ adjgu'.counit.app N)
    {DuS : DX ⥤ DY} {DuS' : SX ⥤ SY} (adjU : DuS ⊣ Lu) (adjU' : DuS' ⊣ Lu') [IsIso αu]
    (eU : Rg ⋙ DuS ⟶ Rgu)
    (heU : ∀ N, adjU.unit.app (Rg.obj N) ≫ Lu.map (eU.app N) ≫ bu.app N = 𝟙 _)
    (eU' : Rg' ⋙ DuS' ⟶ Rgu')
    (heU' : ∀ N, adjU'.unit.app (Rg'.obj N) ≫ Lu'.map (eU'.app N) ≫ bu'.app N = 𝟙 _)
    {L1 : DY ⥤ DY} {Lguh : DY ⥤ DB} {Rguh : DB ⥤ DY} {Lh' : SP ⥤ SY} {Lguh' : SP ⥤ SB}
    {Rguh' : SB ⥤ SP} (adjguh : Lguh ⊣ Rguh) (adjguh' : Lguh' ⊣ Rguh') (c : Lguh ≅ L1 ⋙ Lgu)
    (c' : Lguh' ≅ Lh' ⋙ Lgu') {ΨP : DY ⥤ SP} (αh : ΨP ⋙ Lh' ⟶ L1 ⋙ ΨY)
    (αguh : ΨP ⋙ Lguh' ⟶ Lguh ⋙ ΨB)
    (hαh : ∀ K, αguh.app K ≫ ΨB.map (c.hom.app K) =
      c'.hom.app (ΨP.obj K) ≫ Lgu'.map (αh.app K) ≫ αgu.app (L1.obj K))
    (χguh : Rguh ⋙ ΨP ⟶ ΨB ⋙ Rguh') (hχguh : χguh = (mateEquiv adjguh adjguh' αguh))
    (b : Rguh ⋙ L1 ⟶ Rgu)
    (hb : ∀ N, Lgu.map (b.app N) ≫ adjgu.counit.app N =
      c.inv.app (Rguh.obj N) ≫ adjguh.counit.app N)
    (b' : Rguh' ⋙ Lh' ⟶ Rgu')
    (hb' : ∀ N, Lgu'.map (b'.app N) ≫ adjgu'.counit.app N =
      c'.inv.app (Rguh'.obj N) ≫ adjguh'.counit.app N)
    {Dh : SY ⥤ SP} (e : 𝟭 DY ≅ L1) (adjH : Dh ⊣ Lh') [IsIso αh] (eh : Rgu ⋙ 𝟭 DY ⟶ Rguh)
    (heh : ∀ N, (Adjunction.id.ofNatIsoRight e).unit.app (Rgu.obj N) ≫ L1.map (eh.app N) ≫
      b.app N = 𝟙 _)
    (eH' : Rgu' ⋙ Dh ⟶ Rguh')
    (heH' : ∀ N, adjH.unit.app (Rgu'.obj N) ≫ Lh'.map (eH'.app N) ≫ b'.app N = 𝟙 _)
    {Rp : DY ⥤ DS} {Rp' : SP ⥤ SS} {Rpall : DB ⥤ DS} {Rpall' : SB ⥤ SS} {ΨS : DS ⥤ SS}
    (χp : Rp ⋙ ΨS ⟶ ΨP ⋙ Rp') (χpall : Rpall ⋙ ΨS ⟶ ΨB ⋙ Rpall')
    (conj : Rpall ≅ Rguh ⋙ Rp) (conj' : Rpall' ≅ Rguh' ⋙ Rp')
    (hcomp : ∀ E, χpall.app E ≫ conj'.hom.app (ΨB.obj E) =
      ΨS.map (conj.hom.app E) ≫ χp.app (Rguh.obj E) ≫ Rp'.map (χguh.app E))
    (N : DB) [Mono (bu'.app (ΨB.obj N))] [Mono (b'.app (ΨB.obj N))] :
    ∀ χ₀ : (ΨP ⋙ Rp').obj (Rgu.obj N) ⟶ (Rp ⋙ ΨS).obj (Rgu.obj N),
      χ₀ ≫ χp.app (Rgu.obj N) = 𝟙 _ →
        Rp'.map (Dh.map ((lowerShriekExchangeOfInv adjU adjU' αu).app (Rg.obj N) ≫
            ΨY.map (eU.app N))) ≫
          Rp'.map ((pointOpenExchange adjH e αh).app (Rgu.obj N)) ≫ χ₀ ≫
          ΨS.map (Rp.map ((eh : Rgu ⟶ Rguh).app N) ≫ conj.inv.app N) ≫ χpall.app N =
        Rp'.map (Dh.map (DuS'.map (χg.app N) ≫ eU'.app (ΨB.obj N)) ≫ eH'.app (ΨB.obj N)) ≫
          conj'.inv.app (ΨB.obj N) := fun χ₀ hχ₀ ↦
  map_comp_exchange_aux Dh Rp'
    (lowerShriekExchangeOfInv_app_comp_aux adjg adjgu adjg' adjgu' cu cu' αg αu αgu hαu χg hχg
      χgu hχgu bu hbu bu' hbu' adjU adjU' eU heU eU' heU' N)
    (pointOpenExchange_app_eq adjH e αh _)
    (compactSupportExchange_comp_aux adjgu adjguh adjgu' adjguh' c c' αgu αh αguh hαh χgu hχgu
      χguh hχguh b hb b' hb' (Adjunction.id.ofNatIsoRight e) adjH eh heh eH' heH' χp χpall conj
      conj' hcomp N χ₀ hχ₀)

end Abstract

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

section ModelExchange

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {B B' C C' P P' : Scheme.{u}} {MB : NearbyCyclesModel B B'} {MC : NearbyCyclesModel C C'}
  {MP : NearbyCyclesModel P P'} {g : B ⟶ C} {g' : B' ⟶ C'} {h : C ⟶ P} {h' : C' ⟶ P'}
  {hg : B ⟶ P} {hg' : B' ⟶ P'}

/-- **The exchange `ν_h` of an open immersion on pushforwards**, on the ambient derived
categories: `χ_{hg} ∘ Ψ_P(e) ∘ ν_h(g_* N) = e' ∘ h'_!(χ_g)` for `e = closedExtension`. -/
theorem NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app (φg : MB.Hom MC g g')
    (φh : MC.Hom MP h h') (φhg : MB.Hom MP hg hg') (w : g ≫ h = hg) (w' : g' ≫ h' = hg')
    (htot : φg.total ≫ φh.total = φhg.total) (hgen : φg.generic ≫ φh.generic = φhg.generic)
    {Dh : 𝔻(C) ⥤ 𝔻(P)} {Dh' : 𝔻(C') ⥤ 𝔻(P')} (adj : Dh ⊣ L((h)^*⟦Λ⟧))
    (adj' : Dh' ⊣ L((h')^*⟦Λ⟧)) [IsIso (φh.pullbackExchange Λ)]
    [Mono h] [WeaklyEtale h] [Mono h'] [WeaklyEtale h'] (N : 𝔻(B)) :
    (lowerShriekExchangeOfInv adj adj' (φh.pullbackExchange Λ)).app (R((g)_*⟦Λ⟧).obj N) ≫
        (MP.nearbyCycles Λ).map ((closedExtension adj w).app N) ≫
        (φhg.pushforwardExchange Λ).app N =
      Dh'.map ((φg.pushforwardExchange Λ).app N) ≫
        (closedExtension adj' w').app ((MB.nearbyCycles Λ).obj N) :=
  lowerShriekExchangeOfInv_app_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ hg) (derivedUpperStarLowerStarAdjunction Λ g')
    (derivedUpperStarLowerStarAdjunction Λ hg') (leftDerivedUpperStarCompOfEq Λ w)
    (leftDerivedUpperStarCompOfEq Λ w') (φg.pullbackExchange Λ) (φh.pullbackExchange Λ)
    (φhg.pullbackExchange Λ) (φg.pullbackExchange_comp_app_of_eq Λ φh φhg w w' htot hgen)
    (φg.pushforwardExchange Λ) rfl (φhg.pushforwardExchange Λ) rfl (closedBaseChange Λ w)
    (map_closedBaseChange_app_comp_counit Λ w) (closedBaseChange Λ w')
    (map_closedBaseChange_app_comp_counit Λ w') adj adj' (closedExtension adj w)
    (unit_comp_closedExtension_app adj w) (closedExtension adj' w')
    (unit_comp_closedExtension_app adj' w') N

end ModelExchange

section PointModelExchange

/-- **The ambient identity of `ν_X` on pushforwards**, for morphisms of models
`φ_g : M_B ⟶ 𝒳`, `φ_u : 𝒳 ⟶ 𝒴` (over an open immersion `u`), `φ_h : 𝒴 ⟶ 𝒫` (over `𝟙 Y`, with an
open immersion `h'` of special fibres) and `φ_p : 𝒫 ⟶ 𝒮`: for every right inverse `χ₀` of the
pushforward exchange of `φ_p` at `(gu)_* N`, `Rp'_* h'_!(ν_u) ∘ Rp'_*(ν_h) ∘ χ₀` read through
`closedExtension` is the pushforward exchange of the composite after `Rp'_* h'_! u'_!(χ_g)`. -/
theorem NearbyCyclesModel.Hom.pointExchange_comp_app
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {_ : MonObj Λ} {_ : IsCommMonObj Λ}
    {B B' X X' Y Y' P' S S' : Scheme.{u}} {MB : NearbyCyclesModel B B'}
    {MX : NearbyCyclesModel X X'} {MY : NearbyCyclesModel Y Y'} {MP : NearbyCyclesModel Y P'}
    {MS : NearbyCyclesModel S S'} {g : B ⟶ X} {g' : B' ⟶ X'} {u : X ⟶ Y} {u' : X' ⟶ Y'}
    {h' : Y' ⟶ P'} {p : Y ⟶ S} {p' : P' ⟶ S'} (φg : MB.Hom MX g g') (φu : MX.Hom MY u u')
    (φh : MY.Hom MP (𝟙 Y) h') (φp : MP.Hom MS p p') {DuS : 𝔻(X) ⥤ 𝔻(Y)}
    {DuS' : 𝔻(X') ⥤ 𝔻(Y')} {Dh : 𝔻(Y') ⥤ 𝔻(P')} (adjU : DuS ⊣ L((u)^*⟦Λ⟧))
    (adjU' : DuS' ⊣ L((u')^*⟦Λ⟧)) (adjH : Dh ⊣ L((h')^*⟦Λ⟧)) (e : 𝟭 𝔻(Y) ≅ L((𝟙 Y)^*⟦Λ⟧))
    {_ : IsIso (φu.pullbackExchange Λ)} {_ : IsIso (φh.pullbackExchange Λ)} {_ : Mono u}
    {_ : WeaklyEtale u} {_ : Mono u'} {_ : WeaklyEtale u'} {_ : Mono h'} {_ : WeaklyEtale h'}
    (N : 𝔻(B)) :
    ∀ χ₀ : (MP.nearbyCycles Λ ⋙ R((p')_*⟦Λ⟧)).obj (R((g ≫ u)_*⟦Λ⟧).obj N) ⟶
        (R((p)_*⟦Λ⟧) ⋙ MS.nearbyCycles Λ).obj (R((g ≫ u)_*⟦Λ⟧).obj N),
      χ₀ ≫ (φp.pushforwardExchange Λ).app (R((g ≫ u)_*⟦Λ⟧).obj N) = 𝟙 _ →
        R((p')_*⟦Λ⟧).map (Dh.map ((lowerShriekExchangeOfInv adjU adjU'
            (φu.pullbackExchange Λ)).app (R((g)_*⟦Λ⟧).obj N) ≫
            (MY.nearbyCycles Λ).map ((closedExtension adjU rfl).app N))) ≫
          R((p')_*⟦Λ⟧).map ((pointOpenExchange adjH e (φh.pullbackExchange Λ)).app
            (R((g ≫ u)_*⟦Λ⟧).obj N)) ≫ χ₀ ≫
          (MS.nearbyCycles Λ).map (R((p)_*⟦Λ⟧).map
              ((closedExtension (Adjunction.id.ofNatIsoRight e) rfl :
                R((g ≫ u)_*⟦Λ⟧) ⟶ R(((g ≫ u) ≫ 𝟙 Y)_*⟦Λ⟧)).app N) ≫
            (lowerStarCompOfEq (Λ := Λ) (rfl : ((g ≫ u) ≫ 𝟙 Y) ≫ p = _)).inv.app N) ≫
          ((((φg.comp φu).comp φh).comp φp).pushforwardExchange Λ).app N =
        R((p')_*⟦Λ⟧).map (Dh.map (DuS'.map ((φg.pushforwardExchange Λ).app N) ≫
            (closedExtension adjU' rfl).app ((MB.nearbyCycles Λ).obj N)) ≫
            (closedExtension adjH rfl).app ((MB.nearbyCycles Λ).obj N)) ≫
          (lowerStarCompOfEq (Λ := Λ) (rfl : ((g' ≫ u') ≫ h') ≫ p' = _)).inv.app
            ((MB.nearbyCycles Λ).obj N) :=
  pointExchange_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ (g ≫ u)) (derivedUpperStarLowerStarAdjunction Λ g')
    (derivedUpperStarLowerStarAdjunction Λ (g' ≫ u')) (leftDerivedUpperStarCompOfEq Λ rfl)
    (leftDerivedUpperStarCompOfEq Λ rfl) (φg.pullbackExchange Λ) (φu.pullbackExchange Λ)
    ((φg.comp φu).pullbackExchange Λ)
    (φg.pullbackExchange_comp_app_of_eq Λ φu (φg.comp φu) rfl rfl rfl rfl)
    (φg.pushforwardExchange Λ) rfl ((φg.comp φu).pushforwardExchange Λ) rfl
    (closedBaseChange Λ rfl) (map_closedBaseChange_app_comp_counit Λ rfl)
    (closedBaseChange Λ rfl) (map_closedBaseChange_app_comp_counit Λ rfl) adjU adjU'
    (closedExtension adjU rfl) (unit_comp_closedExtension_app adjU rfl)
    (closedExtension adjU' rfl) (unit_comp_closedExtension_app adjU' rfl)
    (derivedUpperStarLowerStarAdjunction Λ ((g ≫ u) ≫ 𝟙 Y))
    (derivedUpperStarLowerStarAdjunction Λ ((g' ≫ u') ≫ h'))
    (leftDerivedUpperStarCompOfEq Λ rfl) (leftDerivedUpperStarCompOfEq Λ rfl)
    (φh.pullbackExchange Λ) (((φg.comp φu).comp φh).pullbackExchange Λ)
    ((φg.comp φu).pullbackExchange_comp_app_of_eq Λ φh ((φg.comp φu).comp φh) rfl rfl rfl rfl)
    (((φg.comp φu).comp φh).pushforwardExchange Λ) rfl (closedBaseChange Λ rfl)
    (map_closedBaseChange_app_comp_counit Λ rfl) (closedBaseChange Λ rfl)
    (map_closedBaseChange_app_comp_counit Λ rfl) e adjH
    (closedExtension (Adjunction.id.ofNatIsoRight e) rfl)
    (unit_comp_closedExtension_app (Adjunction.id.ofNatIsoRight e) rfl)
    (closedExtension adjH rfl) (unit_comp_closedExtension_app adjH rfl)
    (φp.pushforwardExchange Λ) ((((φg.comp φu).comp φh).comp φp).pushforwardExchange Λ)
    (lowerStarCompOfEq rfl) (lowerStarCompOfEq rfl)
    (((φg.comp φu).comp φh).pushforwardExchange_comp_app_of_eq Λ φp _ rfl rfl rfl rfl) N

/-- `NearbyCyclesModel.Hom.pointExchange_comp_app` with the composite morphism of models `φ`, the
second occurrence `adjH'` of the adjunction of `h'` and the source `R(gu)_*` of the component of
`closedExtension` at `𝟙 Y` given separately, so that its statement can be matched syntactically
with the instances of `openPointExchangeAux_app_comp_aux_of_eq` (see the implementation notes of
`PointExchangeOnComponentBdc`). -/
theorem NearbyCyclesModel.Hom.pointExchange_comp_app_of_eq
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {_ : MonObj Λ} {_ : IsCommMonObj Λ}
    {B B' X X' Y Y' P' S S' : Scheme.{u}} {MB : NearbyCyclesModel B B'}
    {MX : NearbyCyclesModel X X'} {MY : NearbyCyclesModel Y Y'} {MP : NearbyCyclesModel Y P'}
    {MS : NearbyCyclesModel S S'} {g : B ⟶ X} {g' : B' ⟶ X'} {u : X ⟶ Y} {u' : X' ⟶ Y'}
    {h' : Y' ⟶ P'} {p : Y ⟶ S} {p' : P' ⟶ S'} (φg : MB.Hom MX g g') (φu : MX.Hom MY u u')
    (φh : MY.Hom MP (𝟙 Y) h') (φp : MP.Hom MS p p')
    (φ : MB.Hom MS (((g ≫ u) ≫ 𝟙 Y) ≫ p) (((g' ≫ u') ≫ h') ≫ p'))
    (hφ : φ = ((φg.comp φu).comp φh).comp φp) {DuS : 𝔻(X) ⥤ 𝔻(Y)}
    {DuS' : 𝔻(X') ⥤ 𝔻(Y')} {Dh : 𝔻(Y') ⥤ 𝔻(P')} (adjU : DuS ⊣ L((u)^*⟦Λ⟧))
    (adjU' : DuS' ⊣ L((u')^*⟦Λ⟧)) (adjH adjH' : Dh ⊣ L((h')^*⟦Λ⟧)) (hH : adjH = adjH')
    (e : 𝟭 𝔻(Y) ≅ L((𝟙 Y)^*⟦Λ⟧))
    {_ : IsIso (φu.pullbackExchange Λ)} {_ : IsIso (φh.pullbackExchange Λ)} {_ : Mono u}
    {_ : WeaklyEtale u} {_ : Mono u'} {_ : WeaklyEtale u'} {_ : Mono h'} {_ : WeaklyEtale h'}
    (N : 𝔻(B)) :
    ∀ χ₀ : (MP.nearbyCycles Λ ⋙ R((p')_*⟦Λ⟧)).obj (R((g ≫ u)_*⟦Λ⟧).obj N) ⟶
        (R((p)_*⟦Λ⟧) ⋙ MS.nearbyCycles Λ).obj (R((g ≫ u)_*⟦Λ⟧).obj N),
      χ₀ ≫ (φp.pushforwardExchange Λ).app (R((g ≫ u)_*⟦Λ⟧).obj N) = 𝟙 _ →
        R((p')_*⟦Λ⟧).map (Dh.map ((lowerShriekExchangeOfInv adjU adjU'
            (φu.pullbackExchange Λ)).app (R((g)_*⟦Λ⟧).obj N) ≫
            (MY.nearbyCycles Λ).map ((closedExtension adjU rfl).app N))) ≫
          R((p')_*⟦Λ⟧).map ((pointOpenExchange adjH e (φh.pullbackExchange Λ)).app
            (R((g ≫ u)_*⟦Λ⟧).obj N)) ≫ χ₀ ≫
          (MS.nearbyCycles Λ).map (R((p)_*⟦Λ⟧).map
              (@NatTrans.app _ _ _ _ R((g ≫ u)_*⟦Λ⟧) R(((g ≫ u) ≫ 𝟙 Y)_*⟦Λ⟧)
                (closedExtension (Adjunction.id.ofNatIsoRight e) rfl) N) ≫
            (lowerStarCompOfEq (Λ := Λ) (rfl : ((g ≫ u) ≫ 𝟙 Y) ≫ p = _)).inv.app N) ≫
          (φ.pushforwardExchange Λ).app N =
        R((p')_*⟦Λ⟧).map (Dh.map (DuS'.map ((φg.pushforwardExchange Λ).app N) ≫
            (closedExtension adjU' rfl).app ((MB.nearbyCycles Λ).obj N)) ≫
            (closedExtension adjH' rfl).app ((MB.nearbyCycles Λ).obj N)) ≫
          (lowerStarCompOfEq (Λ := Λ) (rfl : ((g' ≫ u') ≫ h') ≫ p' = _)).inv.app
            ((MB.nearbyCycles Λ).obj N) := by
  subst hφ hH
  exact pointExchange_comp_app φg φu φh φp adjU adjU' adjH e N

end PointModelExchange

section Lift

variable {DA DA' DB DB' : Type*} [Category DA] [Category DA'] [Category DB] [Category DB']
  {PA : ObjectProperty DA} {PA' : ObjectProperty DA'} {PB : ObjectProperty DB}
  {PB' : ObjectProperty DB'} {DuS : DA ⥤ DB} {RuA : DB ⥤ DA} {DuS' : DA' ⥤ DB'}
  {RuA' : DB' ⥤ DA'} {ΨA : DA ⥤ DA'} {ΨB : DB ⥤ DB'}

/-- The mate of the inverse of a lifted pullback exchange (`NearbyCyclesModel.liftExchange`) for
the restrictions of adjunctions `u_! ⊣ u^*` to full subcategories is, through the inclusions, the
ambient `lowerShriekExchangeOfInv`. -/
lemma map_mateEquiv_inv_liftExchange (adj : DuS ⊣ RuA) (adj' : DuS' ⊣ RuA')
    (hL : ∀ Z : PA.FullSubcategory, PB ((PA.ι ⋙ DuS).obj Z))
    (hR : ∀ Z : PB.FullSubcategory, PA ((PB.ι ⋙ RuA).obj Z))
    (hL' : ∀ Z : PA'.FullSubcategory, PB' ((PA'.ι ⋙ DuS').obj Z))
    (hR' : ∀ Z : PB'.FullSubcategory, PA' ((PB'.ι ⋙ RuA').obj Z))
    (hA : ∀ Z : PA.FullSubcategory, PA' ((PA.ι ⋙ ΨA).obj Z))
    (hB : ∀ Z : PB.FullSubcategory, PB' ((PB.ι ⋙ ΨB).obj Z))
    (α : ΨB ⋙ RuA' ⟶ RuA ⋙ ΨA) [IsIso α]
    (hα : IsIso (NearbyCyclesModel.liftExchange α hB hA hR' hR)) (K : PA.FullSubcategory) :
    PB'.ι.map (((mateEquiv
        (adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso _ hL).symm (PA.liftCompιIso _ hR).symm)
        (adj'.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
          (PB'.liftCompιIso _ hL').symm (PA'.liftCompιIso _ hR').symm)).symm
          (TwoSquare.mk _ _ _ _ (inv (NearbyCyclesModel.liftExchange α hB hA hR' hR)))).app
          K) =
      (PB'.liftCompιIso _ hL').hom.app ((PA'.lift _ hA).obj K) ≫
        DuS'.map ((PA'.liftCompιIso _ hA).hom.app K) ≫
        (lowerShriekExchangeOfInv adj adj' α).app K.obj ≫
        ΨB.map ((PB.liftCompιIso _ hL).inv.app K) ≫
        (PB'.liftCompιIso _ hB).inv.app ((PB.lift _ hL).obj K) := by
  have f1 := Adjunction.map_restrictFullyFaithful_unit_app adj PA.fullyFaithfulι
    PB.fullyFaithfulι (PB.liftCompιIso _ hL).symm (PA.liftCompιIso _ hR).symm K
  have f2 := Adjunction.map_restrictFullyFaithful_counit_app adj' PA'.fullyFaithfulι
    PB'.fullyFaithfulι (PB'.liftCompιIso _ hL').symm (PA'.liftCompιIso _ hR').symm
    ((PB'.lift (PB.ι ⋙ ΨB) hB).obj ((PB.lift (PA.ι ⋙ DuS) hL).obj K))
  simp only [ObjectProperty.liftCompιIso, Iso.refl_symm, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp,
    ObjectProperty.ι_map] at f1 f2
  simp [mateEquiv, lowerShriekExchangeOfInv, ObjectProperty.hom_inv, ObjectProperty.liftCompιIso,
    f1, f2]

end Lift

section Point

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left] (k' : Type u) [Field k'] [Algebra k k']

/-- The morphism of special fibres of the deformations along the open immersion `u`. -/
noncomputable abbrev pointSpecialMap :=
  deformationSpecialFibreMap u (ker_compatible_of_isOpenImmersion x u) k'

/-- The open immersion of deformation models along `u : X ⊂ Y` (ideals of `x` and `x ≫ u`). Its
type is written with `pointSpecialMap`, so that all the terms built from it carry the same form of
the morphism of special fibres (see the implementation notes of `PointExchangeOnComponentBdc`).
-/
noncomputable abbrev pointModelHom :
    (deformationModel X x.left.ker k').Hom (deformationModel Y (x ≫ u).left.ker k') u.left
      (pointSpecialMap x u k').left :=
  deformationModelHom u (ker_compatible_of_isOpenImmersion x u) k'

instance isIso_pointModelHom_pullbackExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsIso ((pointModelHom x u k').pullbackExchange Λ) :=
  isIso_deformationModelHom_pullbackExchange u _ k' Λ (ker_eq_comap_of_isOpenImmersion x u)

instance isOpenImmersion_pointSpecialMap : IsOpenImmersion (pointSpecialMap x u k').left :=
  have : IsOpenImmersion (pointModelHom x u k').total :=
    isOpenImmersion_deformationTotalMap u _ k' (ker_eq_comap_of_isOpenImmersion x u)
  MorphismProperty.of_isPullback (IsPullback.of_right (by
      rw [Over.w, deformationTotalMap_toTrait]
      exact (isPullback_deformationSpecialFibre X _ k').flip)
    (deformationSpecialFibreMap_toTotal u _ k')
    (isPullback_deformationSpecialFibre Y _ k').flip).flip this

variable [IsProper Y.hom] {B : Over (Spec (.of k))} {B' : Scheme.{u}}
  {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
  {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}

/-- The composite morphism of models `𝒟_B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` over the structure map of `B`. -/
noncomputable abbrev pointCompModelHom (φg : MB.Hom (deformationModel X x.left.ker k') g.left g') :=
  ((φg.comp (pointModelHom x u k')).comp (deformationToCompactifiedModelHom Y (x ≫ u) k')).comp
    (compactifiedToPointModelHom Y (x ≫ u) k')

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {ℓ : ℕ}
  [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]
  (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')

/-- **The exchange `ν_X` on pushforwards from `B`** (step (B) of Varshavsky's argument for `ν_X`):
the instance of `openPointExchangeAux_app_comp_aux_of_eq` for `ν_X`, `G = g_*`, `e_u, e'_u, e'_h`
(`closedExtension`) and the proper exchange of `pointCompModelHom`, given the ambient identity
`hC` (a consequence of `lowerShriekExchangeOfInv_comp_app` and
`compactSupportExchange_comp_app`, see the implementation notes). -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∀ hC, type_of% (
      openPointExchangeAux_app_comp_aux_of_eq _ _ _ _ _ _ _
      (ObjectProperty.fullyFaithfulι _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (pointCompactSupportExchangeOfOpenImmersion (ℓ := ℓ) x u k') rfl
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension
        (Adjunction.id.ofNatIsoRight
          (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ (deformationSpecialFibreToCompactified Y (x ≫ u)
        k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj ℓ (g ≫ u) N⟩
      (Iso.refl _)
      hC
      ) :=
  fun hC ↦ openPointExchangeAux_app_comp_aux_of_eq _ _ _ _ _ _ _
      (ObjectProperty.fullyFaithfulι _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (pointCompactSupportExchangeOfOpenImmersion (ℓ := ℓ) x u k') rfl
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension
        (Adjunction.id.ofNatIsoRight
          (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ (deformationSpecialFibreToCompactified Y (x ≫ u)
        k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj ℓ (g ≫ u) N⟩
      (Iso.refl _)
      hC

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
