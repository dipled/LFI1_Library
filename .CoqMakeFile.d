Utils.vo Utils.glob Utils.v.beautified Utils.required_vo: Utils.v 
Utils.vio: Utils.v 
Utils.vos Utils.vok Utils.required_vos: Utils.v 
Language.vo Language.glob Language.v.beautified Language.required_vo: Language.v Utils.vo
Language.vio: Language.v Utils.vio
Language.vos Language.vok Language.required_vos: Language.v Utils.vos
Semantics.vo Semantics.glob Semantics.v.beautified Semantics.required_vo: Semantics.v Language.vo
Semantics.vio: Semantics.v Language.vio
Semantics.vos Semantics.vok Semantics.required_vos: Semantics.v Language.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v Language.vo
Syntax.vio: Syntax.v Language.vio
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v Language.vos
