/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ClopenCounit
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClass
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity

/-!

# The unit identity of fact (III) on a clopen component

Fact (III) of `ComponentClassReduction` was reduced
(`unitClass_comp_map_comp_lowerShriekCompOfEq_inv`) to the identity
`s ≫ ψ = η_r(ℚ̄_ℓ) ≫ Rr_*(ε⁻¹ ≫ σ_B)` on the special fixed locus `F'`, where
`s = σ_F ≫ Ψ_F(e)⁻¹`, `ψ = Lι'^*(χ_{ιj}) ≫ counit`. This file proves it:

* abstractly (`specializationUnit_comp_inv_map_comp_eq_aux`), for adjunctions standing for
  `Lj^* ⊣ Rj_*`, `Lι^* ⊣ Rι_*`, `L(ιj)^* ⊣ R(ιj)_*`, `Lr^* ⊣ Rr_*`, `Lι'^* ⊣ Rι'_*`,
  `Lb''^* ⊣ Rb''_*`: `Ψ_F(e)` is inverted by `Ψ_F(η_j ≫ Rj_*(ε⁻¹) ≫ (Rj_! ≅ Rj_*)⁻¹)`
  (`ProEtale.CondensedRing.homEquiv_symm_unitIso_inv_comp_unit`), the units of the adjunctions
  compose (`ProEtale.CondensedRing.lowerStarUnit_comp`), and the unit identity of the pushforward
  exchange `χ` and the triangle identity of `Lι'^* ⊣ Rι'_*` conclude;
* for any morphism `φ` of nearby cycles models over `ι ∘ j` whose morphism of special fibres is
  `ι' ∘ r` (`ProEtale.CondensedRing.specializationUnit_comp_inv_map_comp_exchange_eq`), and then
  fact (III) itself (`ProEtale.CondensedRing.unitClass_comp_map_comp_exchange_eq`).

## Implementation notes

For the concrete data (`φ = componentModelHom`, `r = componentSpecialLift`, `ι'` the inclusion of
the special fixed locus) the two theorems are obtained inside a proof by
`have h := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
(hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
(hc.componentSpecialLift_ι k' j hb) hI`
(about 10 seconds). Stating the concrete instance as a public theorem did not finish: the header
`type_of% …` of a public theorem (but not of a `private theorem` or an `example`) runs for more
than 5 minutes. The composition isomorphism `Rb''_* ≅ Rr_* ⋙ Rι'_*` must be the named
`boundedConstructibleLowerStarCompOfEq`: with an inline `eqToHom (by rw [w]) ≫ …` in both the
data and the lemma, the kernel times out comparing the two `eqToHom` terms. With the objects of
the units `eB, …` left implicit (determined by `Functor.Monoidal.εIso`), the kernel times out on
the unit identity of `χ`, so they are passed as `𝟙_ _`. These units then use the monoidal structure
of the full subcategory, while the objects of `εIso` use the projection of
`monoidalCategory_boundedConstructible`; the kernel does not finish comparing the statement of
`lowerStarUnit_comp_of_eq` with the hypothesis `hc'` (it does for `lowerStarUnit_comp` and `hc`),
so `hc'` is proved in place by the proof of `lowerStarUnit_comp_of_eq`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {DB DF DC DB' DF' DC' : Type*} [Category DB] [Category DF] [Category DC]
  [Category DB'] [Category DF'] [Category DC']

/-- The abstract unit identity of fact (III): for adjunctions `aj, aι, af, ar, aι', ab`
(`Lj^* ⊣ Rj_*`, …), compositions `c : jL ⋙ ιL ⟶ fL`, `c' : bL ⟶ rL ⋙ ι'L` compatible with the
units `hc`, `hc'`, an exchange `χ` with unit identity `hunit` and a map `e : jS eB ⟶ eF` with
`e ≫ η_j ≫ jL(εj⁻¹) = I` (`he`) and `Ψ_F(e)` invertible,
`(σ_F ≫ Ψ_F(e)⁻¹) ≫ ψ = η_r ≫ rL(εr⁻¹ ≫ σB)` for
`σ_F = ε_{ι'} ≫ ι'U(σC ≫ ΨC(η_ι)) ≫ ι'U(ΨC(ιL ει⁻¹))` and
`ψ = ι'U(ΨC(ιL(I) ≫ c) ≫ χ ≫ c') ≫ counit`. -/
lemma specializationUnit_comp_inv_map_comp_eq_aux
    {jU : DF ⥤ DB} {jL : DB ⥤ DF} (aj : jU ⊣ jL) {ιU : DC ⥤ DF} {ιL : DF ⥤ DC} (aι : ιU ⊣ ιL)
    {fU : DC ⥤ DB} {fL : DB ⥤ DC} (af : fU ⊣ fL) {rU : DF' ⥤ DB'} {rL : DB' ⥤ DF'}
    (ar : rU ⊣ rL) {ι'U : DC' ⥤ DF'} {ι'L : DF' ⥤ DC'} (aι' : ι'U ⊣ ι'L)
    {bU : DC' ⥤ DB'} {bL : DB' ⥤ DC'} (ab : bU ⊣ bL)
    {ΨC : DC ⥤ DC'} {ΨB : DB ⥤ DB'} (χ : fL ⋙ ΨC ⟶ ΨB ⋙ bL)
    {eB : DB} {eF : DF} {eC : DC} {eB' : DB'} {eF' : DF'} {eC' : DC'}
    (εj : eB ≅ jU.obj eF) (ει : eF ≅ ιU.obj eC) (εf : eB ≅ fU.obj eC)
    (εr : eB' ≅ rU.obj eF') (ει' : eF' ≅ ι'U.obj eC') (εb : eB' ≅ bU.obj eC')
    (c : jL ⋙ ιL ⟶ fL) (c' : bL ⟶ rL ⋙ ι'L)
    (hc : aι.unit.app eC ≫ ιL.map ει.inv ≫ ιL.map (aj.unit.app eF ≫ jL.map εj.inv) ≫
      c.app eB = af.unit.app eC ≫ fL.map εf.inv)
    (hc' : ab.unit.app eC' ≫ bL.map εb.inv ≫ c'.app eB' =
      aι'.unit.app eC' ≫ ι'L.map ει'.inv ≫ ι'L.map (ar.unit.app eF' ≫ rL.map εr.inv))
    (σC : eC' ⟶ ΨC.obj eC) (σB : eB' ⟶ ΨB.obj eB)
    (hunit : σC ≫ ΨC.map (af.unit.app eC) ≫ χ.app (fU.obj eC) =
      ab.unit.app eC' ≫ bL.map (εb.inv ≫ σB ≫ ΨB.map εf.hom))
    {jS : DB ⥤ DF} (I : jS ≅ jL) (e : jS.obj eB ⟶ eF)
    (he : e ≫ aj.unit.app eF ≫ jL.map εj.inv = I.hom.app eB)
    (hI : IsIso ((ιL ⋙ ΨC ⋙ ι'U).map e)) :
    ((ει'.hom ≫ ι'U.map (σC ≫ ΨC.map (aι.unit.app eC)) ≫ ι'U.map (ΨC.map (ιL.map ει.inv))) ≫
        inv ((ιL ⋙ ΨC ⋙ ι'U).map e)) ≫
      ι'U.map (ΨC.map (ιL.map (I.hom.app eB) ≫ c.app eB) ≫ χ.app eB ≫ c'.app (ΨB.obj eB)) ≫
        aι'.counit.app (rL.obj (ΨB.obj eB)) =
      ar.unit.app eF' ≫ rL.map (εr.inv ≫ σB) := by
  set t := aj.unit.app eF ≫ jL.map εj.inv ≫ I.inv.app eB with ht
  have het : e ≫ t = 𝟙 _ := by rw [ht, reassoc_of% he, Iso.hom_inv_id_app]
  have hinv : inv ((ιL ⋙ ΨC ⋙ ι'U).map e) = (ιL ⋙ ΨC ⋙ ι'U).map t :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← Functor.map_comp, het, CategoryTheory.Functor.map_id])
  have h1 : ιL.map t ≫ ιL.map (I.hom.app eB) = ιL.map (aj.unit.app eF ≫ jL.map εj.inv) := by
    rw [← ιL.map_comp, ht, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hχ := χ.naturality εf.inv
  simp only [Functor.comp_map] at hχ
  have hn := c'.naturality σB
  simp only [Functor.comp_map] at hn
  have hX : σC ≫ ΨC.map (aι.unit.app eC ≫ ιL.map ει.inv ≫ ιL.map t ≫ ιL.map (I.hom.app eB) ≫
      c.app eB) ≫ χ.app eB ≫ c'.app (ΨB.obj eB) =
      aι'.unit.app eC' ≫ ι'L.map (ει'.inv ≫ ar.unit.app eF' ≫ rL.map (εr.inv ≫ σB)) := by
    rw [reassoc_of% h1, hc, ΨC.map_comp, Category.assoc, reassoc_of% hχ, reassoc_of% hunit,
      ← bL.map_comp_assoc]
    simp only [Category.assoc, ← ΨB.map_comp, Iso.hom_inv_id, ΨB.map_id, Category.comp_id]
    rw [bL.map_comp_assoc, hn, reassoc_of% hc']
    simp only [Functor.map_comp, Category.assoc]
  rw [hinv]
  have hX' := congrArg ι'U.map hX
  simp only [Functor.map_comp, Category.assoc] at hX'
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hX']
  have hcn := aι'.counit.naturality (ει'.inv ≫ ar.unit.app eF' ≫ rL.map (εr.inv ≫ σB))
  simp only [Functor.comp_map, Functor.id_map] at hcn
  simp only [Functor.map_comp, Category.assoc] at hcn ⊢
  rw [hcn, aι'.left_triangle_components_assoc, Iso.hom_inv_id_assoc]

end Abstract

open Scheme

section LowerStarUnit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The units `ℚ̄_ℓ ⟶ Rf_* Lf^* ℚ̄_ℓ ≅ Rf_* ℚ̄_ℓ` compose along `R(f ≫ g)_* ≅ Rg_* Rf_*`. -/
lemma lowerStarUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ g).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)).inv ≫
      (boundedConstructibleLowerStar ℓ g).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          f).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ f).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)).inv) ≫
      (boundedConstructibleLowerStarComp ℓ f g).hom.app (𝟙_ _) =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (f ≫ g)).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ (f ≫ g)).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g))).inv := by
  have h := unitClass_comp_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (Iso.refl _)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (Iso.refl _)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    (Iso.refl _)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g)
    (boundedConstructibleLowerStarComp ℓ f g)
    (by rw [boundedConstructibleLowerStarComp, Iso.symm_inv, conjugateIsoEquiv_apply_hom,
      Iso.symm_hom])
    (boundedConstructibleLowerStarComp ℓ f g).symm
    (fun K ↦ by simp)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g))
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)))
    (boundedConstructibleUpperStarComp_hom_app_unit ℓ f g)
  simpa using h

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ Rh_*` for a morphism `h` equal to `f ≫ g`. -/
noncomputable def boundedConstructibleLowerStarCompOfEq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    boundedConstructibleLowerStar ℓ f ⋙
        boundedConstructibleLowerStar ℓ g ≅
      boundedConstructibleLowerStar ℓ h :=
  boundedConstructibleLowerStarComp ℓ f g ≪≫ eqToIso (by rw [w])

/-- `lowerStarUnit_comp` for a morphism `h` equal to `f ≫ g`, in the form of the hypothesis `hc'`
of `specializationUnit_comp_inv_map_comp_eq_aux`. -/
lemma lowerStarUnit_comp_of_eq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        h).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ h).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)).inv ≫
      (boundedConstructibleLowerStarCompOfEq ℓ f g w).inv.app (𝟙_ _) =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ g).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)).inv ≫
      (boundedConstructibleLowerStar ℓ g).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          f).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ f).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)).inv) := by
  subst w
  rw [← reassoc_of% (lowerStarUnit_comp ℓ f g)]
  simp [boundedConstructibleLowerStarCompOfEq]

end LowerStarUnit

section Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {B F C : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  {B' F' C' : Over (Spec (.of k'))} [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom]
  [IsSeparated B'.hom] [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom] [IsSeparated F'.hom]
  [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom] [IsSeparated C'.hom]
  (j : B ⟶ F) [IsOpenImmersion j.left] [IsProper j.left] (ι : F ⟶ C)
  {M : NearbyCyclesModel B.left B'.left} {N : NearbyCyclesModel C.left C'.left} {g' : B' ⟶ C'}
  (φ : M.Hom N (j ≫ ι).left g'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (r : B' ⟶ F') (ι' : F' ⟶ C') (w : r ≫ ι' = g')

/-- **The unit identity of fact (III), for a morphism of models over a clopen component**: for
an open and closed immersion `j : B ⟶ F`, a closed `ι : F ⟶ C`, a morphism `φ` of nearby cycles
models over `ι ∘ j` with morphism of special fibres `g' = ι' ∘ r`, with
`Ψ_F = Lι'^* Ψ_N Rι_*`, `σ_F = Lι'^*(Ψ_N(η_ι) σ_N)` and `e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` the adjoint of
`ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ` (with `Ψ_F(e)` invertible), the composite of `σ_F ≫ Ψ_F(e)⁻¹` with
`Lι'^*(Ψ_N(Rι_* Rj_! ≅ R(ιj)_*) ≫ χ_φ ≫ (Rg'_* ≅ Rι'_* Rr_*))` and the counit of
`Lι'^* ⊣ Rι'_*` is `η_r ≫ Rr_*(ε⁻¹ ≫ σ_M)`. -/
theorem specializationUnit_comp_inv_map_comp_exchange_eq
    (hI : IsIso ((boundedConstructibleLowerStar ℓ ι ⋙
      NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι').map
        (((boundedConstructibleUpperShriekAdjunction ℓ
          j).homEquiv _ _).symm (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv))) :
    type_of% (specializationUnit_comp_inv_map_comp_eq_aux
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (j ≫ ι))
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ ι')
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ g')
      (φ.boundedConstructiblePushforwardExchange ℓ hM hN)
      (eB := 𝟙_ _) (eF := 𝟙_ _) (eC := 𝟙_ _) (eB' := 𝟙_ _) (eF' := 𝟙_ _) (eC' := 𝟙_ _)
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι))
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ ι)))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι'))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'))
      (boundedConstructibleLowerStarComp ℓ j ι).hom
      (boundedConstructibleLowerStarCompOfEq ℓ r ι' w).inv
      (lowerStarUnit_comp ℓ j ι) (lowerStarUnit_comp_of_eq ℓ r ι' w)
      (NearbyCyclesModel.boundedConstructibleUnit ℓ hN)
      (NearbyCyclesModel.boundedConstructibleUnit ℓ hM)
      (φ.boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app ℓ hM hN)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j) _
      (homEquiv_symm_unitIso_inv_comp_unit ℓ j) hI) := by
  have h := specializationUnit_comp_inv_map_comp_eq_aux
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (j ≫ ι))
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ ι')
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ g')
      (φ.boundedConstructiblePushforwardExchange ℓ hM hN)
      (eB := 𝟙_ _) (eF := 𝟙_ _) (eC := 𝟙_ _) (eB' := 𝟙_ _) (eF' := 𝟙_ _) (eC' := 𝟙_ _)
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι))
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ ι)))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι'))
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'))
      (boundedConstructibleLowerStarComp ℓ j ι).hom
      (boundedConstructibleLowerStarCompOfEq ℓ r ι' w).inv
      (lowerStarUnit_comp ℓ j ι) ?hc'
      (NearbyCyclesModel.boundedConstructibleUnit ℓ hN)
      (NearbyCyclesModel.boundedConstructibleUnit ℓ hM)
      (φ.boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app ℓ hM hN)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j) _
      (homEquiv_symm_unitIso_inv_comp_unit ℓ j) hI
  · exact h
  -- `lowerStarUnit_comp_of_eq ℓ r ι' w` has the right type up to the instance path of the unit
  -- objects, but the kernel does not finish comparing it with the hypothesis; its proof, run on
  -- the hypothesis itself, is checked at once.
  case hc' =>
    subst w
    rw [← reassoc_of% (lowerStarUnit_comp ℓ r ι')]
    simp [boundedConstructibleLowerStarCompOfEq]

set_option linter.overlappingInstances false in
/-- **Fact (III) for a morphism of models over a clopen component**: with the data of
`specializationUnit_comp_inv_map_comp_exchange_eq`, if `B'`, `F'` and `r` are proper, the map
`Ra_{F'!}(s ≫ ψ)` (`s = σ_F ≫ Ψ_F(e)⁻¹`, `ψ` the exchange composite), read through
`Rr_* ≅ Rr_!` and `Ra_{F'!} Rr_! ≅ Ra_{B'!}`, maps the unit class `[F']` to `Ra_{B'!}(σ_M) [B']`
(`unitClass_comp_map_comp_lowerShriekCompOfEq_inv`). -/
theorem unitClass_comp_map_comp_exchange_eq [IsProper B'.hom] [IsProper F'.hom]
    [IsProper r.left]
    (hI : IsIso ((boundedConstructibleLowerStar ℓ ι ⋙
      NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι').map
        (((boundedConstructibleUpperShriekAdjunction ℓ
          j).homEquiv _ _).symm (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv))) :
    type_of% (unitClass_comp_map_comp_lowerShriekCompOfEq_inv ℓ r _ _ _
      (specializationUnit_comp_inv_map_comp_exchange_eq ℓ j ι φ hM hN r ι' w hI)) := by
  have h := unitClass_comp_map_comp_lowerShriekCompOfEq_inv ℓ r _ _ _
    (specializationUnit_comp_inv_map_comp_exchange_eq ℓ j ι φ hM hN r ι' w hI)
  exact h

end Generic

end AlgebraicGeometry.ProEtale.CondensedRing
