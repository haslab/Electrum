module chapter6/mediaAssets

sig ApplicationState {
	catalogs: set Catalog,
	catalogState: catalogs -> one CatalogState,
	currentCatalog: catalogs,
	buffer: set Asset
	}

sig Catalog, Asset {}

sig CatalogState {
	assets: set Asset,
	disj hidden, showing: set assets,
	selection: set assets + Undefined
	} {
	hidden+showing = assets
	}

one sig Undefined {}

pred catalogInv [cs: CatalogState] {
	cs.selection = Undefined or (some cs.selection and cs.selection in cs.showing)
	}

pred appInv [xs: ApplicationState] {
	all cs: xs.catalogs | catalogInv [xs.catalogState[cs]]
	}

pred showSelected [cs, cs1: CatalogState] {
	cs.selection != Undefined
	cs1.showing = cs.selection
	cs1.selection = cs.selection
	cs1.assets = cs.assets
	}

pred hideSelected [cs, cs1: CatalogState] {
	cs.selection != Undefined
	cs1.hidden = cs.hidden + cs.selection
	cs1.selection = Undefined
	cs1.assets = cs.assets
	}

pred cut [xs, xs1: ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), sel = cs.selection {
		sel != Undefined
		xs1.buffer = sel
		some cs1: CatalogState {
			cs1.assets = cs.assets - sel
			cs1.showing = cs.showing - sel
			cs1.selection = Undefined
			xs1.catalogState = xs.catalogState ++ xs.currentCatalog -> cs1
			}
		}
	xs1.catalogs = xs.catalogs
	xs1.currentCatalog = xs.currentCatalog
	}

pred paste [xs, xs1: ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), buf = xs.buffer {
		xs1.buffer = buf
		some cs1: CatalogState {
			cs1.assets = cs.assets + buf
			cs1.showing = cs.showing + (buf - cs.assets)
			cs1.selection = buf - cs.assets
			xs1.catalogState = xs.catalogState ++ xs.currentCatalog -> cs1
			}
		}
	xs1.catalogs = xs.catalogs
	xs1.currentCatalog = xs.currentCatalog
	}

assert HidePreservesInv {
	all cs, cs1: CatalogState |
		catalogInv [cs] and hideSelected [cs, cs1] => catalogInv [cs1]
	}

// This check should not find any counterexample
check HidePreservesInv

pred sameApplicationState [xs, xs1: ApplicationState] {
	xs1.catalogs = xs.catalogs
	all c: xs.catalogs | sameCatalogState [c.(xs.catalogState), c.(xs1.catalogState)]
	xs1.currentCatalog = xs.currentCatalog
	xs1.buffer = xs.buffer
	}

pred sameCatalogState [cs, cs1: CatalogState] {
	cs1.assets = cs.assets
	cs1.showing = cs.showing
	cs1.selection = cs.selection
	}

assert CutPaste {
	all xs, xs1, xs": ApplicationState |
		(appInv [xs] and cut [xs, xs1] and paste [xs1, xs"]) => sameApplicationState [xs, xs"] 
	}

// This check should find a counterexample
check CutPaste

assert PasteCut {
	all xs, xs1, xs": ApplicationState |
		(appInv [xs] and paste [xs, xs1] and cut [xs1, xs"]) => sameApplicationState [xs, xs"] 
	}

// This check should find a counterexample
check PasteCut

assert PasteNotAffectHidden {
	all xs, xs1: ApplicationState |
		(appInv [xs] and paste [xs, xs1]) => 
			let c = xs.currentCatalog | xs1.catalogState[c].hidden = xs.catalogState[c].hidden
	}

// This check should not find any counterexample
check PasteNotAffectHidden
