/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Trace specialization from the exchange of the support

Let `c` be an endocorrespondence over `k` (the generic fibre) and `c'` one over `k'` (the special
fibre), with fixed loci `ι : F ⟶ C` and `ι' : F' ⟶ C'`. The specialization data
`TraceSpecialization` of blueprint `proposition-specialization-trace-class` consists of
specialization functors `Ψ_C, Ψ_F, Ψ_X, Ψ_{X×X}`, units `σ`, dualizing maps `θ` and exchange maps
`χ`, `β`, with three coherences.

The specialization of the fixed locus can be read off the specialization of the support: since
`ι` and `ι'` are closed immersions, `Ψ_F ≅ Lι'^* Ψ_C Rι_*` for nearby cycles, through the proper
exchange `χ_ι`. Taking this as the *definition* of `Ψ_F`, the data attached to the fixed locus
are determined by those of the support:
* `χ_ι : Ψ_C Rι_* ⟶ Rι'_* Lι'^* Ψ_C Rι_*` is the unit of `Lι'^* ⊣ Rι'_*`;
* `σ_F` is `Lι'^*` of `Ψ_C(η_ι) σ_C`;
* `β_d` is `Lι'^*` of the composite `B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*) ∘ Ψ_C(B⁻¹)` followed by the counit,
  where `B : c^! RΔ_* ≅ Rι_* d^!` is the base change of the fixed square;
* `θ_F = d'^! θ_X ∘ β_d(ω_X)` read through the composition isomorphisms of the dualizing complexes.

With these choices the three coherences of `TraceSpecialization` hold by the triangle identities
of `Lι'^* ⊣ Rι'_*` (`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`).
What remains to be given is the specialization `Ψ_C` of the support with its unit `σ_C`, the
specializations `Ψ_X`, `Ψ_{X×X}` with any transformation `χ_Δ`, the exceptional exchange `β_c` of
the support map and the dualizing map `θ_X`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`: the
  specialization data determined by the data of the support.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

namespace TraceSpecialization

section Abstract

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R)

include adj in
/-- The unit identity behind `ofSupportExchange`, for an arbitrary adjunction `L ⊣ R`: for
`h : A₀ ⟶ A₁` and isomorphisms `e : B ≅ L A₀`, `u : L A₁ ≅ Q`, the square
```
  A₀ ------------h------------> A₁
  |                              |
  η                              η
  v                              v
  R L A₀ --R(e⁻¹ (e L(h) u) u⁻¹)--> R L A₁
```
commutes, by naturality of the unit. -/
lemma comp_unit_app_eq_unit_app_comp_map_conj {A₀ A₁ : 𝒞} (h : A₀ ⟶ A₁) {B : 𝒟}
    (e : B ≅ L.obj A₀) {Q : 𝒟} (u : L.obj A₁ ≅ Q) :
    h ≫ adj.unit.app A₁ = adj.unit.app A₀ ≫ R.map (e.inv ≫ (e.hom ≫ L.map h ≫ u.hom) ≫ u.inv) := by
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact adj.unit.naturality h

/-- The fixed-square identity behind `ofSupportExchange`, for an arbitrary adjunction `L ⊣ R`:
the transpose of `L(b⁻¹ ≫ g) ≫ ε` along the unit, precomposed with `b`, is `g`, that is, the
triangle
```
  A₀ --b--> A --η--> R L A
   \                   |
    g                R(L(b⁻¹ g) ε)
     \                 v
      `-----------> R Y
```
commutes. -/
lemma hom_comp_unit_app_comp_map_counit {A₀ A : 𝒞} {Y : 𝒟} (b : A₀ ≅ A) (g : A₀ ⟶ R.obj Y) :
    b.hom ≫ adj.unit.app A ≫ R.map (L.map (b.inv ≫ g) ≫ adj.counit.app Y) = g := by
  rw [R.map_comp, adj.unit_naturality_assoc, adj.right_triangle_components, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- Naturality of the transpose `L(p) ≫ ε : L P ⟶ T` of a natural transformation
`p : P ⟶ T ⋙ R`: for `g : M ⟶ N` the square
```
  L P M --L(P g)--> L P N
    |                 |
  L(p) ε           L(p) ε
    v                 v
   T M  ---T g--->   T N
```
commutes. -/
lemma map_comp_counit_naturality {𝒜 : Type*} [Category 𝒜] {P : 𝒜 ⥤ 𝒞} {T : 𝒜 ⥤ 𝒟}
    (p : P ⟶ T ⋙ R) {M N : 𝒜} (g : M ⟶ N) :
    L.map (P.map g) ≫ L.map (p.app N) ≫ adj.counit.app (T.obj N) =
      (L.map (p.app M) ≫ adj.counit.app (T.obj M)) ≫ T.map g := by
  rw [← L.map_comp_assoc, p.naturality, L.map_comp_assoc, Functor.comp_map, Category.assoc]
  exact congrArg _ (adj.counit_naturality (T.map g))

/-- The composite `B' ∘ c'(χ) ∘ β(Δ) ∘ Ψ(B⁻¹)` of four natural transformations
`B⁻¹ : D ⋙ I ⟶ Δ ⋙ c`, `β : c ⋙ Ψ ⟶ Ψ₂ ⋙ c'`, `χ : Δ ⋙ Ψ₂ ⟶ Ψ₁ ⋙ Δ'` and
`B' : Δ' ⋙ c' ⟶ D' ⋙ I'`, for arbitrary functors. -/
@[simps]
def fourExchange {𝒜 𝒜₁ 𝒜' 𝒜₁' ℬ ℬ' 𝒞' : Type*} [Category 𝒜] [Category 𝒜₁] [Category 𝒜']
    [Category 𝒜₁'] [Category ℬ] [Category ℬ'] [Category 𝒞'] {D : 𝒜 ⥤ 𝒜₁} {I : 𝒜₁ ⥤ 𝒞}
    {Ψ : 𝒞 ⥤ 𝒞'} {Δ : 𝒜 ⥤ ℬ} {c : ℬ ⥤ 𝒞} {Ψ₂ : ℬ ⥤ ℬ'} {c' : ℬ' ⥤ 𝒞'} {Ψ₁ : 𝒜 ⥤ 𝒜'}
    {Δ' : 𝒜' ⥤ ℬ'} {D' : 𝒜' ⥤ 𝒜₁'} {I' : 𝒜₁' ⥤ 𝒞'} (Binv : D ⋙ I ⟶ Δ ⋙ c)
    (β : c ⋙ Ψ ⟶ Ψ₂ ⋙ c') (χ : Δ ⋙ Ψ₂ ⟶ Ψ₁ ⋙ Δ') (B' : Δ' ⋙ c' ⟶ D' ⋙ I') :
    (D ⋙ I) ⋙ Ψ ⟶ (Ψ₁ ⋙ D') ⋙ I' where
  app M := Ψ.map (Binv.app M) ≫ β.app (Δ.obj M) ≫ c'.map (χ.app M) ≫ B'.app (Ψ₁.obj M)
  naturality M N g := by
    have h₁ := Binv.naturality g
    have h₂ := β.naturality (Δ.map g)
    have h₃ := χ.naturality g
    have h₄ := B'.naturality (Ψ₁.map g)
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ h₄ ⊢
    rw [← Ψ.map_comp_assoc, h₁, Ψ.map_comp_assoc, reassoc_of% h₂, ← c'.map_comp_assoc, h₃,
      c'.map_comp_assoc, h₄]
    simp only [Category.assoc]

end Abstract

variable (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (βc : boundedConstructibleUpperShriek ℓ c.support ⋙ ΨC ⟶
    ΨXX ⋙ boundedConstructibleUpperShriek ℓ c'.support)

/-- The specialization `Ψ_F = Lι'^* Ψ_C Rι_*` of the fixed locus determined by the specialization
`Ψ_C` of the support. -/
noncomputable abbrev fixedLocusSpecialization :
    Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerStar ℓ F.ι ⋙ ΨC ⋙
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι

/-- The composite `B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*) ∘ Ψ_C(B⁻¹) : Ψ_C Rι_* Rd^! ⟶ Rι'_* Rd'^! Ψ_X` of the
exchange maps of the support with the base change isomorphisms `B : c^! RΔ_* ≅ Rι_* d^!` of the
fixed squares. -/
noncomputable def fixedSquareExchange :
    (boundedConstructibleUpperShriek ℓ F.d ⋙
        boundedConstructibleLowerStar ℓ F.ι) ⋙ ΨC ⟶
      (ΨX ⋙ boundedConstructibleUpperShriek ℓ F'.d) ⋙
        boundedConstructibleLowerStar ℓ F'.ι :=
  fourExchange F.upperShriekLowerStarIso.inv βc χΔ F'.upperShriekLowerStarIso.hom


/-- The exceptional exchange `β_d : Ψ_F Rd^! ⟶ Rd'^! Ψ_X` determined by the exceptional exchange
`β_c` of the support: `Lι'^*` of `fixedSquareExchange`, followed by the counit of
`Lι'^* ⊣ Rι'_*`. -/
noncomputable def fixedLocusExceptionalExchange :
    boundedConstructibleUpperShriek ℓ F.d ⋙
        fixedLocusSpecialization (F := F) (F' := F') ΨC ⟶
      ΨX ⋙ boundedConstructibleUpperShriek ℓ F'.d where
  app M := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map
      ((fixedSquareExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc).app M) ≫
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).counit.app _
  naturality _ _ g := map_comp_counit_naturality
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι)
    (fixedSquareExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc) g

variable (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _))
  (θX : ΨX.obj (dualizingComplex' ℓ X) ⟶ dualizingComplex' ℓ X')

/-- **The specialization data determined by the support** (blueprint
`proposition-specialization-trace-class`): given the specialization `Ψ_C` of the support with its
unit `σ_C`, specializations `Ψ_X`, `Ψ_{X×X}` with a transformation `χ_Δ : Ψ_{X×X} RΔ_* ⟶ RΔ'_* Ψ_X`,
the exceptional exchange `β_c : Ψ_C Rc^! ⟶ Rc'^! Ψ_{X×X}` of the support map and a dualizing map
`θ_X`, the specialization data with
* `Ψ_F = Lι'^* Ψ_C Rι_*` and `χ_ι` the unit of `Lι'^* ⊣ Rι'_*`;
* `σ_F = Lι'^*(Ψ_C(η_ι) σ_C)`, read through the unit isomorphisms of the monoidal pullbacks;
* `β_d = fixedLocusExceptionalExchange` and `θ_F = d'^! θ_X ∘ β_d(ω_X)`.
The coherences hold by the triangle identities of `Lι'^* ⊣ Rι'_*`. -/
noncomputable def ofSupportExchange : c.TraceSpecialization F c' F' where
  ΨC := ΨC
  ΨF := fixedLocusSpecialization (F := F) (F' := F') ΨC
  ΨX := ΨX
  ΨXX := ΨXX
  σC := σC
  σF := (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map
      (σC ≫ ΨC.map ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).unit.app
        (𝟙_ _))) ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).map
      (ΨC.map ((boundedConstructibleLowerStar ℓ F.ι).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).inv))
  θX := θX
  θF := (fixedLocusSpecialization (F := F) (F' := F') ΨC).map
      (dualizingComplexComp ℓ F.d).inv ≫
    (fixedLocusExceptionalExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc).app
      (dualizingComplex' ℓ X) ≫
    (boundedConstructibleUpperShriek ℓ F'.d).map θX ≫
    (dualizingComplexComp ℓ F'.d).hom
  χι :=
    { app N := (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).unit.app
        (ΨC.obj ((boundedConstructibleLowerStar ℓ F.ι).obj N))
      naturality _ _ g :=
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).unit.naturality
        (ΨC.map ((boundedConstructibleLowerStar ℓ F.ι).map g)) }
  χΔ := χΔ
  βc := βc
  βd := fixedLocusExceptionalExchange (F := F) (F' := F') ΨC ΨX ΨXX χΔ βc
  unit_comp := (Category.assoc _ _ _).symm.trans
    (comp_unit_app_eq_unit_app_comp_map_conj
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι) _
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι))
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι).mapIso
        (ΨC.mapIso ((boundedConstructibleLowerStar ℓ F.ι).mapIso
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι)).symm))))
  θF_eq := rfl
  fixedSquare M := hom_comp_unit_app_comp_map_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι)
    (ΨC.mapIso (F.upperShriekLowerStarIso.app M)) _

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
