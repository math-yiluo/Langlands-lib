/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.Coherence

/-!

# The cube coherence of the model Frobenius comparisons

Let `𝒞` be a category (of schemes) with a family of pullback functors `U a : D B ⥤ D A` for
`a : A ⟶ B`, with composition isomorphisms `cU a b : U (a ≫ b) ≅ U b ⋙ U a` satisfying the
associativity law `assocU`.

For a commutative square `w : a ≫ b = c ≫ d` we have the square comparison
`sqIso U cU w : U d ⋙ U c ≅ U b ⋙ U a`. For a base change `π : Xb ⟶ X` and a model Frobenius
`Φ : Xb ⟶ Xb` lying over `g ≫ F` (`Φ ≫ π = π ≫ g ≫ F`) with a trivialization `κ : U F ≅ 𝟭`, we
have the model comparison `modelComparison U cU h κ : U π ⋙ U Φ ≅ U g ⋙ U π`.

Given a morphism `f : X ⟶ Y` with a base change `fb : Xb ⟶ Yb` compatible with all the data, the
main result `modelComparison_cube` states that the cube formed by the two model comparisons and
the square comparisons of `f` commutes. The proof expresses both sides, up to `κ`, through the
canonical isomorphisms `pullbackComp₃Hom` and `pullbackComp₄Hom` of the pullback along a
composite of three or four morphisms.

-/

@[expose] public section

universe v₁ u₁

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {𝒞 : Type*} [Category 𝒞] {D : 𝒞 → Type u₁} [∀ A, Category.{v₁} (D A)]

section Pullback

variable (U : ∀ {A B : 𝒞}, (A ⟶ B) → D B ⥤ D A)
  (cU : ∀ {A B C : 𝒞} (a : A ⟶ B) (b : B ⟶ C), U (a ≫ b) ≅ U b ⋙ U a)

/-- The comparison `U d ⋙ U c ≅ U (c ≫ d) = U (a ≫ b) ≅ U b ⋙ U a` of a commutative square
`w : a ≫ b = c ≫ d`. -/
def sqIso {P Q R S : 𝒞} {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S}
    (w : a ≫ b = c ≫ d) : U d ⋙ U c ≅ U b ⋙ U a :=
  (cU c d).symm ≪≫ pullbackCongrIso U w.symm ≪≫ cU a b

@[simp]
lemma sqIso_hom_app {P Q R S : 𝒞} {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S}
    (w : a ≫ b = c ≫ d) (M : D S) :
    (sqIso U cU w).hom.app M =
      (cU c d).inv.app M ≫ eqToHom (congrArg (fun s ↦ (U s).obj M) w.symm) ≫
        (cU a b).hom.app M :=
  rfl

/-- Naturality of the square comparison, with the composite functors unfolded. -/
@[reassoc]
lemma sqIso_hom_naturality {P Q R S : 𝒞} {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S}
    (w : a ≫ b = c ≫ d) {M M' : D S} (φ : M ⟶ M') :
    (U c).map ((U d).map φ) ≫ (sqIso U cU w).hom.app M' =
      (sqIso U cU w).hom.app M ≫ (U a).map ((U b).map φ) :=
  (sqIso U cU w).hom.naturality φ

/-- The model comparison `U π ⋙ U Φ ≅ U (Φ ≫ π) = U (π ≫ g ≫ F) ≅ U π ⋙ U (g ≫ F)
≅ U π ⋙ U F ⋙ U g --κ--> U π ⋙ U g` of a model Frobenius `Φ` lying over `g ≫ F`
(`h : Φ ≫ π = π ≫ g ≫ F`), for a trivialization `κ : U F ≅ 𝟭`. The last factor is the whiskering
of `Iso.compIsoOfIsoId (cU g F) κ`, unfolded. -/
def modelComparison {P X : 𝒞} {π : P ⟶ X} {Φ : P ⟶ P} {g F : X ⟶ X}
    (h : Φ ≫ π = π ≫ g ≫ F) (κ : U F ≅ 𝟭 (D X)) : U π ⋙ U Φ ≅ U g ⋙ U π :=
  (cU Φ π).symm ≪≫ pullbackCongrIso U h ≪≫ cU π (g ≫ F) ≪≫
    Functor.isoWhiskerRight (cU g F ≪≫ Functor.isoWhiskerRight κ (U g) ≪≫ (U g).leftUnitor)
      (U π)

/-- The components of `modelComparison`. -/
lemma modelComparison_hom_app {P X : 𝒞} {π : P ⟶ X} {Φ : P ⟶ P} {g F : X ⟶ X}
    (h : Φ ≫ π = π ≫ g ≫ F) (κ : U F ≅ 𝟭 (D X)) (M : D X) :
    (modelComparison U cU h κ).hom.app M =
      (cU Φ π).inv.app M ≫ eqToHom (congrArg (fun s ↦ (U s).obj M) h) ≫
        (cU π (g ≫ F)).hom.app M ≫
        (U π).map ((cU g F).hom.app M ≫ (U g).map (κ.hom.app M)) := by
  simp [modelComparison]

/-- The model comparison is the square comparison of `π ≫ (g ≫ F) = Φ ≫ π` followed by `κ`. -/
lemma modelComparison_hom_app_eq_sqIso {P X : 𝒞} {π : P ⟶ X} {Φ : P ⟶ P} {g F : X ⟶ X}
    (h : Φ ≫ π = π ≫ g ≫ F) (κ : U F ≅ 𝟭 (D X)) (M : D X) :
    (modelComparison U cU h κ).hom.app M =
      (sqIso U cU h.symm).hom.app M ≫
        (U π).map ((cU g F).hom.app M ≫ (U g).map (κ.hom.app M)) := by
  simp [modelComparison_hom_app]

/-- The canonical morphism `U (a ≫ b ≫ c) M ⟶ U a U b U c M`. -/
def pullbackComp₃Hom {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (M : D C') :
    (U (a ≫ b ≫ c)).obj M ⟶ (U a).obj ((U b).obj ((U c).obj M)) :=
  (cU a (b ≫ c)).hom.app M ≫ (U a).map ((cU b c).hom.app M)

instance {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (M : D C') :
    IsIso (pullbackComp₃Hom U cU a b c M) := by
  unfold pullbackComp₃Hom
  infer_instance

/-- The canonical morphism `U (a ≫ b ≫ c ≫ d) M ⟶ U a U b U c U d M`. -/
def pullbackComp₄Hom {A B C C' C'' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (d : C' ⟶ C'')
    (M : D C'') :
    (U (a ≫ b ≫ c ≫ d)).obj M ⟶ (U a).obj ((U b).obj ((U c).obj ((U d).obj M))) :=
  (cU a (b ≫ c ≫ d)).hom.app M ≫ (U a).map (pullbackComp₃Hom U cU b c d M)

/-- `pullbackComp₄Hom` through `pullbackComp₃Hom` of the first three factors. -/
lemma pullbackComp₄Hom_eq {A B C C' C'' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C')
    (d : C' ⟶ C'') (M : D C'') :
    pullbackComp₄Hom U cU a b c d M =
      pullbackComp₃Hom U cU a b (c ≫ d) M ≫ (U a).map ((U b).map ((cU c d).hom.app M)) := by
  simp [pullbackComp₄Hom, pullbackComp₃Hom]

/-- Splitting the last factor of a triple composite gives `pullbackComp₄Hom`. -/
@[reassoc]
lemma pullbackComp₃Hom_comp_map_map_hom_app {A B C C' C'' : 𝒞} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ C') (d : C' ⟶ C'') (M : D C'') :
    pullbackComp₃Hom U cU a b (c ≫ d) M ≫ (U a).map ((U b).map ((cU c d).hom.app M)) =
      pullbackComp₄Hom U cU a b c d M :=
  (pullbackComp₄Hom_eq U cU a b c d M).symm

/-- A square comparison on the last two factors of a triple composite. -/
@[reassoc]
lemma pullbackComp₃Hom_comp_map_sqIso_hom_app {P Q R S T : 𝒞} (x : T ⟶ P) {a : P ⟶ Q}
    {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d) (M : D S) :
    pullbackComp₃Hom U cU x c d M ≫ (U x).map ((sqIso U cU w).hom.app M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (by rw [w] : x ≫ c ≫ d = x ≫ a ≫ b)) ≫
        pullbackComp₃Hom U cU x a b M := by
  rw [pullbackComp₃Hom, pullbackComp₃Hom, sqIso_hom_app, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc, Functor.map_comp,
    comp_hom_app_comp_map_eqToHom_aux_assoc U cU x w.symm]

/-- Splitting the middle factor of a triple composite gives `pullbackComp₄Hom`. -/
@[reassoc]
lemma pullbackComp₃Hom_comp_map_hom_app {A B C C' C'' : 𝒞} (x : A ⟶ B) (c : B ⟶ C)
    (d : C ⟶ C') (z : C' ⟶ C'') (M : D C'')
    (assocU : (cU (c ≫ d) z).hom.app M ≫ (cU c d).hom.app ((U z).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc c d z)) ≫
        (cU c (d ≫ z)).hom.app M ≫ (U c).map ((cU d z).hom.app M)) :
    pullbackComp₃Hom U cU x (c ≫ d) z M ≫ (U x).map ((cU c d).hom.app ((U z).obj M)) =
      eqToHom (congrArg (fun s ↦ (U s).obj M)
          (by rw [Category.assoc] : x ≫ (c ≫ d) ≫ z = x ≫ c ≫ d ≫ z)) ≫
        pullbackComp₄Hom U cU x c d z M := by
  rw [pullbackComp₃Hom, Category.assoc ((cU x ((c ≫ d) ≫ z)).hom.app M), ← Functor.map_comp,
    assocU, Functor.map_comp,
    comp_hom_app_comp_map_eqToHom_aux_assoc U cU x (Category.assoc c d z)]
  simp [pullbackComp₄Hom, pullbackComp₃Hom]

variable (assocU : ∀ {A B C C' : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ C') (M : D C'),
    (cU (a ≫ b) c).hom.app M ≫ (cU a b).hom.app ((U c).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (Category.assoc a b c)) ≫
        (cU a (b ≫ c)).hom.app M ≫ (U a).map ((cU b c).hom.app M))

include assocU in
/-- A square comparison on the first two factors of a triple composite. -/
@[reassoc]
lemma pullbackComp₃Hom_comp_sqIso_hom_app {P Q R S T : 𝒞} {a : P ⟶ Q} {b : Q ⟶ S}
    {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d) (x : S ⟶ T) (M : D T) :
    pullbackComp₃Hom U cU c d x M ≫ (sqIso U cU w).hom.app ((U x).obj M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M)
          (by rw [reassoc_of% w] : c ≫ d ≫ x = a ≫ b ≫ x)) ≫
        pullbackComp₃Hom U cU a b x M := by
  rw [pullbackComp₃Hom, sqIso_hom_app, Category.assoc,
    map_hom_app_comp_inv_app_aux_assoc U cU c d x M (assocU _ _ _ _), Iso.hom_inv_id_app_assoc,
    ← eqToHom_comp_comp_hom_app_aux_assoc U cU w.symm x M, assocU a b x M]
  simp [pullbackComp₃Hom]

include assocU in
/-- A square comparison on the first two factors of a quadruple composite. -/
@[reassoc]
lemma pullbackComp₄Hom_comp_sqIso_hom_app {P Q R S T T' : 𝒞} {a : P ⟶ Q} {b : Q ⟶ S}
    {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d) (y : S ⟶ T) (z : T ⟶ T') (M : D T') :
    pullbackComp₄Hom U cU c d y z M ≫ (sqIso U cU w).hom.app ((U y).obj ((U z).obj M)) =
      eqToHom (congrArg (fun s ↦ (U s).obj M)
          (by rw [reassoc_of% w] : c ≫ d ≫ y ≫ z = a ≫ b ≫ y ≫ z)) ≫
        pullbackComp₄Hom U cU a b y z M := by
  rw [pullbackComp₄Hom_eq, pullbackComp₄Hom_eq, Category.assoc]
  erw [sqIso_hom_naturality U cU w]
  rw [pullbackComp₃Hom_comp_sqIso_hom_app_assoc U cU assocU w]

include assocU in
/-- A square comparison on the middle two factors of a quadruple composite. -/
@[reassoc]
lemma pullbackComp₄Hom_comp_map_sqIso_hom_app {P Q R S T T' : 𝒞} (x : T ⟶ P) {a : P ⟶ Q}
    {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d) (z : S ⟶ T') (M : D T') :
    pullbackComp₄Hom U cU x c d z M ≫ (U x).map ((sqIso U cU w).hom.app ((U z).obj M)) =
      eqToHom (congrArg (fun s ↦ (U s).obj M)
          (by rw [reassoc_of% w] : x ≫ c ≫ d ≫ z = x ≫ a ≫ b ≫ z)) ≫
        pullbackComp₄Hom U cU x a b z M := by
  rw [pullbackComp₄Hom, Category.assoc, ← Functor.map_comp,
    pullbackComp₃Hom_comp_sqIso_hom_app U cU assocU w, Functor.map_comp,
    comp_hom_app_comp_map_eqToHom_aux_assoc U cU x
      (by rw [reassoc_of% w] : c ≫ d ≫ z = a ≫ b ≫ z)]
  simp [pullbackComp₄Hom]

/-- A square comparison on the last two factors of a quadruple composite. -/
@[reassoc]
lemma pullbackComp₄Hom_comp_map_map_sqIso_hom_app {P Q R S T T' : 𝒞} (x : T' ⟶ T)
    (y : T ⟶ P) {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S} (w : a ≫ b = c ≫ d)
    (M : D S) :
    pullbackComp₄Hom U cU x y c d M ≫ (U x).map ((U y).map ((sqIso U cU w).hom.app M)) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) (by rw [w] : x ≫ y ≫ c ≫ d = x ≫ y ≫ a ≫ b)) ≫
        pullbackComp₄Hom U cU x y a b M := by
  rw [pullbackComp₄Hom, Category.assoc, ← Functor.map_comp,
    pullbackComp₃Hom_comp_map_sqIso_hom_app, Functor.map_comp,
    comp_hom_app_comp_map_eqToHom_aux_assoc U cU x (by rw [w] : y ≫ c ≫ d = y ≫ a ≫ b)]
  simp [pullbackComp₄Hom]

include assocU in
/-- **The cube coherence of the model comparisons.** Let `πX : Xb ⟶ X` and `πY : Yb ⟶ Y` be base
changes with model Frobenii `ΦX`, `ΦY` lying over `gX ≫ FX` and `gY ≫ FY`, trivializations
`κX : U FX ≅ 𝟭`, `κY : U FY ≅ 𝟭`, and let `f : X ⟶ Y` with base change `fb : Xb ⟶ Yb` be
compatible with all the data (`hκ` being the compatibility of `κX` and `κY` along `f`). Then the
two composites `U fb U ΦY U πY N ⟶ U πX U gX U f N` through the model comparisons and the square
comparisons of `f` agree. -/
theorem modelComparison_cube {Xb Yb X Y : 𝒞} {πX : Xb ⟶ X} {πY : Yb ⟶ Y} {fb : Xb ⟶ Yb}
    {f : X ⟶ Y} {gX FX : X ⟶ X} {gY FY : Y ⟶ Y} {ΦX : Xb ⟶ Xb} {ΦY : Yb ⟶ Yb}
    (hπ : fb ≫ πY = πX ≫ f) (hΦX : ΦX ≫ πX = πX ≫ gX ≫ FX) (hΦY : ΦY ≫ πY = πY ≫ gY ≫ FY)
    (hg : gX ≫ f = f ≫ gY) (hF : f ≫ FY = FX ≫ f) (hΦ : ΦX ≫ fb = fb ≫ ΦY)
    (κX : U FX ≅ 𝟭 (D X)) (κY : U FY ≅ 𝟭 (D Y))
    (hκ : ∀ M : D Y, (cU f FY).hom.app M ≫ (U f).map (κY.hom.app M) =
      eqToHom (congrArg (fun s ↦ (U s).obj M) hF) ≫ (cU FX f).hom.app M ≫
        κX.hom.app ((U f).obj M))
    (N : D Y) :
    (U fb).map ((modelComparison U cU hΦY κY).hom.app N) ≫
        (sqIso U cU hπ.symm).hom.app ((U gY).obj N) ≫ (U πX).map ((sqIso U cU hg).hom.app N) =
      (sqIso U cU hΦ).hom.app ((U πY).obj N) ≫ (U ΦX).map ((sqIso U cU hπ.symm).hom.app N) ≫
        (modelComparison U cU hΦX κX).hom.app ((U f).obj N) := by
  have hκ' : (U f).map (κY.hom.app N) =
      (sqIso U cU hF.symm).hom.app N ≫ κX.hom.app ((U f).obj N) := by
    rw [sqIso_hom_app]
    simp only [Category.assoc]
    rw [← hκ, Iso.inv_hom_id_app_assoc]
  rw [← cancel_epi (pullbackComp₃Hom U cU fb ΦY πY N), modelComparison_hom_app_eq_sqIso,
    modelComparison_hom_app_eq_sqIso]
  simp only [Functor.map_comp, Category.assoc]
  erw [sqIso_hom_naturality_assoc U cU hπ.symm]
  simp only [Functor.comp_obj]
  conv_lhs =>
    rw [← (U πX).map_comp]
    erw [sqIso_hom_naturality U cU hg]
    rw [Functor.map_comp, hκ', Functor.map_comp, Functor.map_comp]
  rw [pullbackComp₃Hom_comp_map_sqIso_hom_app_assoc, pullbackComp₃Hom_comp_map_map_hom_app_assoc,
    pullbackComp₄Hom_comp_sqIso_hom_app_assoc U cU assocU,
    pullbackComp₄Hom_comp_map_sqIso_hom_app_assoc U cU assocU,
    pullbackComp₄Hom_comp_map_map_sqIso_hom_app_assoc,
    pullbackComp₃Hom_comp_sqIso_hom_app_assoc U cU assocU,
    pullbackComp₃Hom_comp_map_sqIso_hom_app_assoc,
    pullbackComp₃Hom_comp_sqIso_hom_app_assoc U cU assocU,
    pullbackComp₃Hom_comp_map_hom_app_assoc U cU _ _ _ _ _ (assocU _ _ _ _)]
  simp only [eqToHom_trans_assoc]

end Pullback

end AlgebraicGeometry.ProEtale.CondensedRing
