/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMilnor
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleMittagLeffler
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLimitEpimorphicTower
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLowerStarDerivedLimit

/-!
# The Milnor sequence for derived pushforwards of towers of pro-étale sheaves

Let `f : X ⟶ Y` be a morphism of schemes and let `(Tₙ)` be a tower of complexes of sheaves of
`Λ`-modules on `X_proét` with degreewise epimorphic transitions (e.g. an `ℓ`-adic tower
`Gₙ = G_{n+1}/ℓⁿ` of sheaves of `ℤ/ℓⁿ`-modules, viewed as sheaves of `ℤ`-modules). Then
`lim Tₙ = R lim Tₙ` (`AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_Q_of_epi`), `Rf_*`
commutes with `R lim` (`AlgebraicGeometry.ProEtale.isHomotopyLimit_rightDerivedLowerStar_mapCone`)
and the Milnor sequence of the homotopy limit
(`DerivedCategory.shortExact_milnor_of_isHomotopyLimit`) gives, for `i + 1 = j`,
```
  0 ⟶ R¹lim Rⁱf_* Tₙ ⟶ Rʲf_* (lim Tₙ) ⟶ lim Rʲf_* Tₙ ⟶ 0
```
(blueprint `proposition-milnor-sequence`, `proposition-milnor-sequence--2`, Stacks 0CQD). If the
tower `(Rⁱf_* Tₙ)ₙ` is Mittag-Leffler, the `R¹lim` term vanishes
(`CategoryTheory.GrothendieckTopology.epi_one_sub_of_mittagLeffler_imageSubobject`) and
`Rʲf_* (lim Tₙ) ≅ lim Rʲf_* Tₙ`.

## Main results

- `AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar`: the Milnor sequence.
- `AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler`:
  `Rʲf_* (lim Tₙ) ≅ lim Rʲf_* Tₙ` when `(Rⁱf_* Tₙ)ₙ` is Mittag-Leffler (images stabilise).
- `AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_forall_mittagLeffler`:
  the same when the section towers over affine weakly contractible objects are Mittag-Leffler.
- `AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar_single`: the Milnor
  sequence for a tower of sheaves (complexes in degree `0`) with epimorphic transitions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated DerivedCategory

namespace AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Functor

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The Milnor sequence for `Rf_*` of a tower of pro-étale sheaves** (blueprint
`proposition-milnor-sequence`, Stacks 0CQD). Let `T` be a tower of complexes of sheaves of
`Λ`-modules on `X_proét` with degreewise epimorphic transitions and limit cone `c`, let `i + 1 = j`,
let `P` be a product of the `Rⁱf_* Tₙ` with its transition endomorphism `t` and let `d` be a limit
cone over `n ↦ Rʲf_* Tₙ`. Then there is a short exact sequence of sheaves on `Y_proét`
`0 ⟶ coker (1 - t) ⟶ Rʲf_* (lim Tₙ) ⟶ d.pt ⟶ 0`, i.e.
`0 ⟶ R¹lim Rⁱf_* Tₙ ⟶ Rʲf_* (lim Tₙ) ⟶ lim Rʲf_* Tₙ ⟶ 0`, whose second map is induced by the
projections `lim Tₙ ⟶ Tₙ`. -/
theorem shortExact_milnor_rightDerivedLowerStar
    {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) (i j : ℤ) (hij : i + 1 = j)
    {P : Fan fun n : ℕ ↦ (homologyFunctor _ i).obj
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj (Q.obj (T.obj (op n))))}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ (homologyFunctor _ i).map
      (R((f)_*[ModuleCat.{u + 1} Λ]).map (Q.map (T.map (homOfLE n.le_succ).op))))
    {d : Cone (((T ⋙ Q) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ j)}
    (hd : IsLimit d) :
    ∃ (a : cokernel (𝟙 P.pt - t) ⟶
        (homologyFunctor _ j).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj (Q.obj c.pt)))
      (hz : a ≫ hd.lift ((homologyFunctor _ j).mapCone
        (R((f)_*[ModuleCat.{u + 1} Λ]).mapCone (Q.mapCone c))) = 0),
      (ShortComplex.mk _ _ hz).ShortExact :=
  shortExact_milnor_of_isHomotopyLimit
    (isHomotopyLimit_rightDerivedLowerStar_mapCone _ f (isHomotopyLimit_mapCone_Q_of_epi hT hc))
    i j hij hP t ht hd

/-- **Mittag-Leffler kills the `R¹lim` term**: in the situation of
`AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar`, if the tower of sheaves
`(Rⁱf_* Tₙ)ₙ` on `Y_proét` is Mittag-Leffler (for every `n` there is `N ≥ n` such that the image
of `Rⁱf_* T_N ⟶ Rⁱf_* Tₙ` is contained in the image of `Rⁱf_* Tₖ ⟶ Rⁱf_* Tₙ` for all `k ≥ n`),
then `Rʲf_* (lim Tₙ) ⟶ lim Rʲf_* Tₙ` is an isomorphism. -/
theorem isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler
    {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) (i j : ℤ) (hij : i + 1 = j)
    (hML : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject ((homologyFunctor _ i).map
        (R((f)_*[ModuleCat.{u + 1} Λ]).map (Q.map (T.map (homOfLE hN).op)))) ≤
      imageSubobject ((homologyFunctor _ i).map
        (R((f)_*[ModuleCat.{u + 1} Λ]).map (Q.map (T.map (homOfLE hk).op)))))
    {d : Cone (((T ⋙ Q) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ j)}
    (hd : IsLimit d) :
    IsIso (hd.lift ((homologyFunctor _ j).mapCone
      (R((f)_*[ModuleCat.{u + 1} Λ]).mapCone (Q.mapCone c)))) := by
  let F := ((T ⋙ Q) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ i
  let t : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
    Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  exact isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit
    (isHomotopyLimit_rightDerivedLowerStar_mapCone _ f (isHomotopyLimit_mapCone_Q_of_epi hT hc))
    i j hij (productIsProduct _) t ht
    (GrothendieckTopology.epi_one_sub_of_mittagLeffler_imageSubobject.{u + 1, u}
      (fun W : Y.ProEt ↦ IsAffine W.left ∧
        (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} W)
      (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2)
      (F := F) (productIsProduct _) t ht hML) hd

/-- **Mittag-Leffler on weakly contractible sections kills the `R¹lim` term** (blueprint
`proposition-milnor-sequence`, last paragraph): in the situation of
`AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar`, if over every affine
weakly contractible `W` of `Y_proét` the tower of section modules `(Rⁱf_* Tₙ)(W)` is
Mittag-Leffler, then `Rʲf_* (lim Tₙ) ⟶ lim Rʲf_* Tₙ` is an isomorphism. -/
theorem isIso_lift_homology_rightDerivedLowerStar_of_forall_mittagLeffler
    {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) (i j : ℤ) (hij : i + 1 = j)
    (hML : ∀ W : Y.ProEt, IsAffine W.left →
      (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} W →
      ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
        LinearMap.range (((homologyFunctor _ i).map (R((f)_*[ModuleCat.{u + 1} Λ]).map
          (Q.map (T.map (homOfLE hN).op)))).hom.app (op W)).hom ≤
        LinearMap.range (((homologyFunctor _ i).map (R((f)_*[ModuleCat.{u + 1} Λ]).map
          (Q.map (T.map (homOfLE hk).op)))).hom.app (op W)).hom)
    {d : Cone (((T ⋙ Q) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ j)}
    (hd : IsLimit d) :
    IsIso (hd.lift ((homologyFunctor _ j).mapCone
      (R((f)_*[ModuleCat.{u + 1} Λ]).mapCone (Q.mapCone c)))) := by
  let F := ((T ⋙ Q) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ i
  let t : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
    Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  exact isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit
    (isHomotopyLimit_rightDerivedLowerStar_mapCone _ f (isHomotopyLimit_mapCone_Q_of_epi hT hc))
    i j hij (productIsProduct _) t ht
    (GrothendieckTopology.epi_one_sub_of_forall_mittagLeffler.{u + 1, u}
      (fun W : Y.ProEt ↦ IsAffine W.left ∧
        (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} W)
      (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2)
      (F := F) (productIsProduct _) t ht fun W hW ↦ hML W hW.1 hW.2) hd

omit [CommRing Λ] in
/-- The degreewise components of the image of an epimorphism under `HomologicalComplex.single`
are epimorphisms. -/
lemma epi_single_map_f {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] [HasZeroObject C]
    {A B : C} (g : A ⟶ B) [Epi g] (j i : ℤ) :
    Epi (((HomologicalComplex.single C (ComplexShape.up ℤ) j).map g).f i) := by
  by_cases h : i = j
  · subst h
    rw [HomologicalComplex.single_map_f_self]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X _ j B i h).epi _

/-- **The Milnor sequence for `Rf_*` of a tower of pro-étale sheaves with epimorphic
transitions** (blueprint `proposition-milnor-sequence`): for a tower `G` of sheaves of `Λ`-modules
on `X_proét` with epimorphic transitions (e.g. an `ℓ`-adic tower `G_{n+1}/ℓⁿ ≅ Gₙ`), and
`i + 1 = j`, there is a short exact sequence
`0 ⟶ R¹lim Rⁱf_* Gₙ ⟶ Rʲf_* (lim Gₙ) ⟶ lim Rʲf_* Gₙ ⟶ 0` of sheaves on `Y_proét`, where
`R¹lim` is the cokernel of `1 - t` on a product `P` of the `Rⁱf_* Gₙ`. -/
theorem shortExact_milnor_rightDerivedLowerStar_single
    {G : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE n.le_succ).op)) {c : Cone G} (hc : IsLimit c)
    (i j : ℤ) (hij : i + 1 = j)
    {P : Fan fun n : ℕ ↦ (homologyFunctor _ i).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj
      (Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (G.obj (op n)))))}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ (homologyFunctor _ i).map
      (R((f)_*[ModuleCat.{u + 1} Λ]).map (Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (G.map (homOfLE n.le_succ).op)))))
    {d : Cone ((((G ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0) ⋙ Q) ⋙
      R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ homologyFunctor _ j)}
    (hd : IsLimit d) :
    ∃ (a : cokernel (𝟙 P.pt - t) ⟶ (homologyFunctor _ j).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj
        (Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj c.pt))))
      (hz : a ≫ hd.lift ((homologyFunctor _ j).mapCone (R((f)_*[ModuleCat.{u + 1} Λ]).mapCone
        (Q.mapCone ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone c)))) = 0),
      (ShortComplex.mk _ _ hz).ShortExact := by
  let S := HomologicalComplex.single (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (ComplexShape.up ℤ) 0
  have (n : ℕ) := hG n
  exact shortExact_milnor_rightDerivedLowerStar f (T := G ⋙ S) (c := S.mapCone c)
    (fun n i ↦ epi_single_map_f _ 0 i) (isLimitOfPreserves S hc) i j hij hP t ht hd

end AlgebraicGeometry.ProEtale
