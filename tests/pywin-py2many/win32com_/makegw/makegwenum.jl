#= Utility file for generating PyIEnum support.

This is almost a 'template' file.  It simplay contains almost full
C++ source code for PyIEnum* support, and the Python code simply
substitutes the appropriate interface name.

This module is notmally not used directly - the @makegw@ module
automatically calls this.
 =#
import win32com_.ext_modules.string as string
function is_interface_enum(enumtype)
    return !(enumtype[1] ∈ string.uppercase && enumtype[3] ∈ string.uppercase)
end

function _write_enumifc_cpp(f, interface)
    enumtype = interface.name[6:end]
    if is_interface_enum(enumtype)
        enum_interface = "I" + enumtype[begin:-1]
        converter =
            "PyObject *ob = PyCom_PyObjectFromIUnknown(rgVar[i], IID_%(enum_interface)s, FALSE);" %
            locals()
        arraydeclare =
            "%(enum_interface)s **rgVar = new %(enum_interface)s *[celt];" % locals()
    else
        converter = "PyObject *ob = PyCom_PyObjectFrom%(enumtype)s(&rgVar[i]);" % locals()
        arraydeclare = "%(enumtype)s *rgVar = new %(enumtype)s[celt];" % locals()
    end
    write(
        f,
        "\n// ---------------------------------------------------\n//\n// Interface Implementation\n\nPyIEnum%(enumtype)s::PyIEnum%(enumtype)s(IUnknown *pdisp):\n\tPyIUnknown(pdisp)\n{\n\tob_type = &type;\n}\n\nPyIEnum%(enumtype)s::~PyIEnum%(enumtype)s()\n{\n}\n\n/* static */ IEnum%(enumtype)s *PyIEnum%(enumtype)s::GetI(PyObject *self)\n{\n\treturn (IEnum%(enumtype)s *)PyIUnknown::GetI(self);\n}\n\n// @pymethod object|PyIEnum%(enumtype)s|Next|Retrieves a specified number of items in the enumeration sequence.\nPyObject *PyIEnum%(enumtype)s::Next(PyObject *self, PyObject *args)\n{\n\tlong celt = 1;\n\t// @pyparm int|num|1|Number of items to retrieve.\n\tif ( !PyArg_ParseTuple(args, \"|l:Next\", &celt) )\n\t\treturn NULL;\n\n\tIEnum%(enumtype)s *pIE%(enumtype)s = GetI(self);\n\tif ( pIE%(enumtype)s == NULL )\n\t\treturn NULL;\n\n\t%(arraydeclare)s\n\tif ( rgVar == NULL ) {\n\t\tPyErr_SetString(PyExc_MemoryError, \"allocating result %(enumtype)ss\");\n\t\treturn NULL;\n\t}\n\n\tint i;\n/*\tfor ( i = celt; i--; )\n\t\t// *** possibly init each structure element???\n*/\n\n\tULONG celtFetched = 0;\n\tPY_INTERFACE_PRECALL;\n\tHRESULT hr = pIE%(enumtype)s->Next(celt, rgVar, &celtFetched);\n\tPY_INTERFACE_POSTCALL;\n\tif (  HRESULT_CODE(hr) != ERROR_NO_MORE_ITEMS && FAILED(hr) )\n\t{\n\t\tdelete [] rgVar;\n\t\treturn PyCom_BuildPyException(hr,pIE%(enumtype)s, IID_IE%(enumtype)s);\n\t}\n\n\tPyObject *result = PyTuple_New(celtFetched);\n\tif ( result != NULL )\n\t{\n\t\tfor ( i = celtFetched; i--; )\n\t\t{\n\t\t\t%(converter)s\n\t\t\tif ( ob == NULL )\n\t\t\t{\n\t\t\t\tPy_DECREF(result);\n\t\t\t\tresult = NULL;\n\t\t\t\tbreak;\n\t\t\t}\n\t\t\tPyTuple_SET_ITEM(result, i, ob);\n\t\t}\n\t}\n\n/*\tfor ( i = celtFetched; i--; )\n\t\t// *** possibly cleanup each structure element???\n*/\n\tdelete [] rgVar;\n\treturn result;\n}\n\n// @pymethod |PyIEnum%(enumtype)s|Skip|Skips over the next specified elementes.\nPyObject *PyIEnum%(enumtype)s::Skip(PyObject *self, PyObject *args)\n{\n\tlong celt;\n\tif ( !PyArg_ParseTuple(args, \"l:Skip\", &celt) )\n\t\treturn NULL;\n\n\tIEnum%(enumtype)s *pIE%(enumtype)s = GetI(self);\n\tif ( pIE%(enumtype)s == NULL )\n\t\treturn NULL;\n\n\tPY_INTERFACE_PRECALL;\n\tHRESULT hr = pIE%(enumtype)s->Skip(celt);\n\tPY_INTERFACE_POSTCALL;\n\tif ( FAILED(hr) )\n\t\treturn PyCom_BuildPyException(hr, pIE%(enumtype)s, IID_IE%(enumtype)s);\n\n\tPy_INCREF(Py_None);\n\treturn Py_None;\n}\n\n// @pymethod |PyIEnum%(enumtype)s|Reset|Resets the enumeration sequence to the beginning.\nPyObject *PyIEnum%(enumtype)s::Reset(PyObject *self, PyObject *args)\n{\n\tif ( !PyArg_ParseTuple(args, \":Reset\") )\n\t\treturn NULL;\n\n\tIEnum%(enumtype)s *pIE%(enumtype)s = GetI(self);\n\tif ( pIE%(enumtype)s == NULL )\n\t\treturn NULL;\n\n\tPY_INTERFACE_PRECALL;\n\tHRESULT hr = pIE%(enumtype)s->Reset();\n\tPY_INTERFACE_POSTCALL;\n\tif ( FAILED(hr) )\n\t\treturn PyCom_BuildPyException(hr, pIE%(enumtype)s, IID_IE%(enumtype)s);\n\n\tPy_INCREF(Py_None);\n\treturn Py_None;\n}\n\n// @pymethod <o PyIEnum%(enumtype)s>|PyIEnum%(enumtype)s|Clone|Creates another enumerator that contains the same enumeration state as the current one\nPyObject *PyIEnum%(enumtype)s::Clone(PyObject *self, PyObject *args)\n{\n\tif ( !PyArg_ParseTuple(args, \":Clone\") )\n\t\treturn NULL;\n\n\tIEnum%(enumtype)s *pIE%(enumtype)s = GetI(self);\n\tif ( pIE%(enumtype)s == NULL )\n\t\treturn NULL;\n\n\tIEnum%(enumtype)s *pClone;\n\tPY_INTERFACE_PRECALL;\n\tHRESULT hr = pIE%(enumtype)s->Clone(&pClone);\n\tPY_INTERFACE_POSTCALL;\n\tif ( FAILED(hr) )\n\t\treturn PyCom_BuildPyException(hr, pIE%(enumtype)s, IID_IE%(enumtype)s);\n\n\treturn PyCom_PyObjectFromIUnknown(pClone, IID_IEnum%(enumtype)s, FALSE);\n}\n\n// @object PyIEnum%(enumtype)s|A Python interface to IEnum%(enumtype)s\nstatic struct PyMethodDef PyIEnum%(enumtype)s_methods[] =\n{\n\t{ \"Next\", PyIEnum%(enumtype)s::Next, 1 },    // @pymeth Next|Retrieves a specified number of items in the enumeration sequence.\n\t{ \"Skip\", PyIEnum%(enumtype)s::Skip, 1 },\t// @pymeth Skip|Skips over the next specified elementes.\n\t{ \"Reset\", PyIEnum%(enumtype)s::Reset, 1 },\t// @pymeth Reset|Resets the enumeration sequence to the beginning.\n\t{ \"Clone\", PyIEnum%(enumtype)s::Clone, 1 },\t// @pymeth Clone|Creates another enumerator that contains the same enumeration state as the current one.\n\t{ NULL }\n};\n\nPyComEnumTypeObject PyIEnum%(enumtype)s::type(\"PyIEnum%(enumtype)s\",\n\t\t&PyIUnknown::type,\n\t\tsizeof(PyIEnum%(enumtype)s),\n\t\tPyIEnum%(enumtype)s_methods,\n\t\tGET_PYCOM_CTOR(PyIEnum%(enumtype)s));\n" %
        locals(),
    )
end

function _write_enumgw_cpp(f, interface)
    enumtype = interface.name[6:end]
    if is_interface_enum(enumtype)
        enum_interface = "I" + enumtype[begin:-1]
        converter =
            "if ( !PyCom_InterfaceFromPyObject(ob, IID_%(enum_interface)s, (void **)&rgVar[i], FALSE) )" %
            locals()
        argdeclare = "%(enum_interface)s __RPC_FAR * __RPC_FAR *rgVar" % locals()
    else
        argdeclare = "%(enumtype)s __RPC_FAR *rgVar" % locals()
        converter = "if ( !PyCom_PyObjectAs%(enumtype)s(ob, &rgVar[i]) )" % locals()
    end
    write(
        f,
        "\n// ---------------------------------------------------\n//\n// Gateway Implementation\n\n// Std delegation\nSTDMETHODIMP_(ULONG) PyGEnum%(enumtype)s::AddRef(void) {return PyGatewayBase::AddRef();}\nSTDMETHODIMP_(ULONG) PyGEnum%(enumtype)s::Release(void) {return PyGatewayBase::Release();}\nSTDMETHODIMP PyGEnum%(enumtype)s::QueryInterface(REFIID iid, void ** obj) {return PyGatewayBase::QueryInterface(iid, obj);}\nSTDMETHODIMP PyGEnum%(enumtype)s::GetTypeInfoCount(UINT FAR* pctInfo) {return PyGatewayBase::GetTypeInfoCount(pctInfo);}\nSTDMETHODIMP PyGEnum%(enumtype)s::GetTypeInfo(UINT itinfo, LCID lcid, ITypeInfo FAR* FAR* pptInfo) {return PyGatewayBase::GetTypeInfo(itinfo, lcid, pptInfo);}\nSTDMETHODIMP PyGEnum%(enumtype)s::GetIDsOfNames(REFIID refiid, OLECHAR FAR* FAR* rgszNames, UINT cNames, LCID lcid, DISPID FAR* rgdispid) {return PyGatewayBase::GetIDsOfNames( refiid, rgszNames, cNames, lcid, rgdispid);}\nSTDMETHODIMP PyGEnum%(enumtype)s::Invoke(DISPID dispid, REFIID riid, LCID lcid, WORD wFlags, DISPPARAMS FAR* params, VARIANT FAR* pVarResult, EXCEPINFO FAR* pexcepinfo, UINT FAR* puArgErr) {return PyGatewayBase::Invoke( dispid, riid, lcid, wFlags, params, pVarResult, pexcepinfo, puArgErr);}\n\nSTDMETHODIMP PyGEnum%(enumtype)s::Next( \n            /* [in] */ ULONG celt,\n            /* [length_is][size_is][out] */ %(argdeclare)s,\n            /* [out] */ ULONG __RPC_FAR *pCeltFetched)\n{\n\tPY_GATEWAY_METHOD;\n\tPyObject *result;\n\tHRESULT hr = InvokeViaPolicy(\"Next\", &result, \"i\", celt);\n\tif ( FAILED(hr) )\n\t\treturn hr;\n\n\tif ( !PySequence_Check(result) )\n\t\tgoto error;\n\tint len;\n\tlen = PyObject_Length(result);\n\tif ( len == -1 )\n\t\tgoto error;\n\tif ( len > (int)celt)\n\t\tlen = celt;\n\n\tif ( pCeltFetched )\n\t\t*pCeltFetched = len;\n\n\tint i;\n\tfor ( i = 0; i < len; ++i )\n\t{\n\t\tPyObject *ob = PySequence_GetItem(result, i);\n\t\tif ( ob == NULL )\n\t\t\tgoto error;\n\n\t\t%(converter)s\n\t\t{\n\t\t\tPy_DECREF(result);\n\t\t\treturn PyCom_SetCOMErrorFromPyException(IID_IEnum%(enumtype)s);\n\t\t}\n\t}\n\n\tPy_DECREF(result);\n\n\treturn len < (int)celt ? S_FALSE : S_OK;\n\n  error:\n\tPyErr_Clear();\t// just in case\n\tPy_DECREF(result);\n\treturn PyCom_HandleIEnumNoSequence(IID_IEnum%(enumtype)s);\n}\n\nSTDMETHODIMP PyGEnum%(enumtype)s::Skip( \n            /* [in] */ ULONG celt)\n{\n\tPY_GATEWAY_METHOD;\n\treturn InvokeViaPolicy(\"Skip\", NULL, \"i\", celt);\n}\n\nSTDMETHODIMP PyGEnum%(enumtype)s::Reset(void)\n{\n\tPY_GATEWAY_METHOD;\n\treturn InvokeViaPolicy(\"Reset\");\n}\n\nSTDMETHODIMP PyGEnum%(enumtype)s::Clone( \n            /* [out] */ IEnum%(enumtype)s __RPC_FAR *__RPC_FAR *ppEnum)\n{\n\tPY_GATEWAY_METHOD;\n\tPyObject * result;\n\tHRESULT hr = InvokeViaPolicy(\"Clone\", &result);\n\tif ( FAILED(hr) )\n\t\treturn hr;\n\n\t/*\n\t** Make sure we have the right kind of object: we should have some kind\n\t** of IUnknown subclass wrapped into a PyIUnknown instance.\n\t*/\n\tif ( !PyIBase::is_object(result, &PyIUnknown::type) )\n\t{\n\t\t/* the wrong kind of object was returned to us */\n\t\tPy_DECREF(result);\n\t\treturn PyCom_SetCOMErrorFromSimple(E_FAIL, IID_IEnum%(enumtype)s);\n\t}\n\n\t/*\n\t** Get the IUnknown out of the thing. note that the Python ob maintains\n\t** a reference, so we don\'t have to explicitly AddRef() here.\n\t*/\n\tIUnknown *punk = ((PyIUnknown *)result)->m_obj;\n\tif ( !punk )\n\t{\n\t\t/* damn. the object was released. */\n\t\tPy_DECREF(result);\n\t\treturn PyCom_SetCOMErrorFromSimple(E_FAIL, IID_IEnum%(enumtype)s);\n\t}\n\n\t/*\n\t** Get the interface we want. note it is returned with a refcount.\n\t** This QI is actually going to instantiate a PyGEnum%(enumtype)s.\n\t*/\n\thr = punk->QueryInterface(IID_IEnum%(enumtype)s, (LPVOID *)ppEnum);\n\n\t/* done with the result; this DECREF is also for <punk> */\n\tPy_DECREF(result);\n\n\treturn PyCom_CheckIEnumNextResult(hr, IID_IEnum%(enumtype)s);\n}\n" %
        locals(),
    )
end
