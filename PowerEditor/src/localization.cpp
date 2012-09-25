// This file is part of Notepad++ project
// Copyright (C)2003 Don HO <don.h@free.fr>
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either
// version 2 of the License, or (at your option) any later version.
//
// Note that the GPL places important restrictions on "derived works", yet
// it does not provide a detailed definition of that term.  To avoid      
// misunderstandings, we consider an application to constitute a          
// "derivative work" for the purpose of this license if it does any of the
// following:                                                             
// 1. Integrates source code from Notepad++.
// 2. Integrates/includes/aggregates Notepad++ into a proprietary executable
//    installer, such as those produced by InstallShield.
// 3. Links to a library or executes a program that does any of the above.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


#include "precompiledHeaders.h"
#include "Notepad_plus.h"
#include "ShortcutMapper.h"
#include "EncodingMapper.h"

#include "localization.h"


void NativeLangSpeaker::init(TiXmlDocumentA *nativeLangDocRootA, bool loadIfEnglish)
{
	if (nativeLangDocRootA)
	{
		_nativeLangA =  nativeLangDocRootA->FirstChild("NotepadPlus");
		if (_nativeLangA)
		{
			_nativeLangA = _nativeLangA->FirstChild("Native-Langue");
			if (_nativeLangA)
			{
				TiXmlElementA *element = _nativeLangA->ToElement();
				const char *rtl = element->Attribute("RTL");
				if (rtl)
					_isRTL = (strcmp(rtl, "yes") == 0);
                else
                    _isRTL = false;

                // get original file name (defined by Notpad++) from the attribute
                _fileName = element->Attribute("filename");

				if (!loadIfEnglish && _fileName && stricmp("english.xml", _fileName) == 0)
                {
					_nativeLangA = NULL;
					return;
				}
				// get encoding
				TiXmlDeclarationA *declaration =  _nativeLangA->GetDocument()->FirstChild()->ToDeclaration();
				if (declaration)
				{
					const char * encodingStr = declaration->Encoding();
					EncodingMapper *em = EncodingMapper::getInstance();
                    int enc = em->getEncodingFromString(encodingStr);
                    _nativeLangEncoding = (enc != -1)?enc:CP_ACP;
				}
			}	
		}
    }
}

generic_string NativeLangSpeaker::getSpecialMenuEntryName(const char *entryName)
{
	if (!_nativeLangA) return TEXT("");
	TiXmlNodeA *mainMenu = _nativeLangA->FirstChild("Menu");
	if (!mainMenu) return TEXT("");
	mainMenu = mainMenu->FirstChild("Main");
	if (!mainMenu) return TEXT("");
	TiXmlNodeA *entriesRoot = mainMenu->FirstChild("Entries");
	if (!entriesRoot) return TEXT("");
	const char *idName = NULL;

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	for (TiXmlNodeA *childNode = entriesRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();

		idName = element->Attribute("idName");
		if (idName)
		{
			const char *name = element->Attribute("name");
			if (!strcmp(idName, entryName))
			{
#ifdef UNICODE
				return wmc->char2wchar(name, _nativeLangEncoding);
#else
				return name;
#endif
			}
		}
	}
	return TEXT("");
}

generic_string NativeLangSpeaker::getNativeLangMenuString(int itemID) 
{
	if (!_nativeLangA)
		return TEXT("");

	TiXmlNodeA *node = _nativeLangA->FirstChild("Menu");
	if (!node) return TEXT("");

	node = node->FirstChild("Main");
	if (!node) return TEXT("");

	node = node->FirstChild("Commands");
	if (!node) return TEXT("");

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	for (TiXmlNodeA *childNode = node->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		if (element->Attribute("id", &id) && (id == itemID))
		{
			const char *name = element->Attribute("name");
			if (name)
			{
#ifdef UNICODE
				return wmc->char2wchar(name, _nativeLangEncoding);
#else
				return name;
#endif
			}
		}
	}
	return TEXT("");
}

struct MenuPosition {
	int _x;
	int _y;
	int _z;
	char _id[64];
	//MenuPosition(): _x(-1), _y(-1), _z(-1){_id[0] = '\0';};
};

MenuPosition menuPos[] = {
//==============================================
//  {L0,  L1,  L2,    id},
//==============================================
	{ 0,  -1,  -1,    "file"},
	{ 1,  -1,  -1,    "edit"},
	{ 2,  -1,  -1,    "search"},
	{ 3,  -1,  -1,    "view"},
	{ 4,  -1,  -1,    "encoding"},
	{ 5,  -1,  -1,    "language"},
	{ 6,  -1,  -1,    "settings"},
	{ 7,  -1,  -1,    "macro"},
	{ 8,  -1,  -1,    "run"},

	{ 0,  19,  -1,    "file-recentFiles"},

	{ 1,   9,  -1,    "edit-copyToClipboard"},
	{ 1,  10,  -1,    "edit-indent"},
	{ 1,  11,  -1,    "edit-convertCaseTo"},
	{ 1,  12,  -1,    "edit-lineOperations"},
	{ 1,  13,  -1,    "edit-comment"},
	{ 1,  14,  -1,    "edit-autoCompletion"},
	{ 1,  15,  -1,    "edit-eolConversion"},
	{ 1,  16,  -1,    "edit-blankOperations"},
	{ 1,  17,  -1,    "edit-pasteSpecial"},
	
	{ 2,  16,  -1,    "search-markAll"},
	{ 2,  17,  -1,    "search-unmarkAll"},
	{ 2,  18,  -1,    "search-jumpUp"},
	{ 2,  19,  -1,    "search-jumpDown"},
	{ 2,  21,  -1,    "search-bookmark"},
	
	{ 3,   4,  -1,    "view-showSymbol"},
	{ 3,   5,  -1,    "view-zoom"},
	{ 3,   6,  -1,    "view-moveCloneDocument"},
	{ 3,  16,  -1,    "view-collapsLevel"},
	{ 3,  17,  -1,    "view-uncollapseLevel"},
	{ 3,  21,  -1,    "view-project"},
	
	{ 4,   5,  -1,    "encoding-characterSets"},
	{ 4,   5,   0,    "encoding-arabic"},
	{ 4,   5,   1,    "encoding-baltic"},
	{ 4,   5,   2,    "encoding-celtic"},
	{ 4,   5,   3,    "encoding-cyrillic"},
	{ 4,   5,   4,    "encoding-centralEuropean"},
	{ 4,   5,   5,    "encoding-chinese"},
	{ 4,   5,   6,    "encoding-easternEuropean"},
	{ 4,   5,   7,    "encoding-greek"},
	{ 4,   5,   8,    "encoding-hebrew"},
	{ 4,   5,   9,    "encoding-japanese"},
	{ 4,   5,  10,    "encoding-korean"},
	{ 4,   5,  11,    "encoding-northEuropean"},
	{ 4,   5,  12,    "encoding-thai"},
	{ 4,   5,  13,    "encoding-turkish"},
	{ 4,   5,  14,    "encoding-westernEuropean"},
	{ 4,   5,  15,    "encoding-vietnamese"},

	{ 6,   4,  -1,    "settings-import"},
	{-1,  -1,  -1,    ""} // End of array
};

MenuPosition & getMenuPosition(const char *id) {

	int nbSubMenuPos = sizeof(menuPos)/sizeof(MenuPosition);

	for(int i = 0; i < nbSubMenuPos; i++) 
	{
		if (strcmp(menuPos[i]._id, id) == 0)
			return menuPos[i];
	}
	return menuPos[nbSubMenuPos-1];
};

void NativeLangSpeaker::changeMenuLang(HMENU menuHandle, generic_string & pluginsTrans, generic_string & windowTrans)
{
	if (!_nativeLangA) return;
	TiXmlNodeA *mainMenu = _nativeLangA->FirstChild("Menu");
	if (!mainMenu) return;
	mainMenu = mainMenu->FirstChild("Main");
	if (!mainMenu) return;
	TiXmlNodeA *entriesRoot = mainMenu->FirstChild("Entries");
	if (!entriesRoot) return;
	const char *idName = NULL;

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	for (TiXmlNodeA *childNode = entriesRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		//int id;
		const char *menuIdStr = element->Attribute("menuId");
		//if (element->Attribute("id", &id))
		if (menuIdStr)
		{
			MenuPosition & menuPos = getMenuPosition(menuIdStr);
			if (menuPos._x != -1)
			{
				const char *name = element->Attribute("name");

#ifdef UNICODE
				const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
				::ModifyMenu(menuHandle, menuPos._x, MF_BYPOSITION, 0, nameW);
#else
				::ModifyMenu(menuHandle, menuPos._x, MF_BYPOSITION, 0, name);
#endif
			}
		}
		else 
		{
			idName = element->Attribute("idName");
			if (idName)
			{
				const char *name = element->Attribute("name");
				if (!strcmp(idName, "Plugins"))
				{
#ifdef UNICODE
					const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
					pluginsTrans = nameW;
#else
					pluginsTrans = name;
#endif
				}
				else if (!strcmp(idName, "Window"))
				{
#ifdef UNICODE
					const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
					windowTrans = nameW;
#else
					windowTrans = name;
	#endif
				}
			}
		}
	}

	TiXmlNodeA *menuCommandsRoot = mainMenu->FirstChild("Commands");
	for (TiXmlNodeA *childNode = menuCommandsRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		element->Attribute("id", &id);
		const char *name = element->Attribute("name");

#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
		::ModifyMenu(menuHandle, id, MF_BYCOMMAND, id, nameW);
#else
		::ModifyMenu(menuHandle, id, MF_BYCOMMAND, id, name);
#endif
	}

	TiXmlNodeA *subEntriesRoot = mainMenu->FirstChild("SubEntries");

	for (TiXmlNodeA *childNode = subEntriesRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int x, y, z;
		//const char *xStr = element->Attribute("posX", &x);
		//const char *yStr = element->Attribute("posY", &y);
		const char *subMenuIdStr = element->Attribute("subMenuId");
		const char *name = element->Attribute("name");

		if (!subMenuIdStr || !name)
			continue;

		MenuPosition & menuPos = getMenuPosition(subMenuIdStr);
		x = menuPos._x;
		y = menuPos._y;
		z = menuPos._z;

		HMENU hSubMenu = ::GetSubMenu(menuHandle, x);
		if (!hSubMenu)
			continue;
		HMENU hSubMenu2 = ::GetSubMenu(hSubMenu, y);
		if (!hSubMenu2)
			continue;

		HMENU hMenu = hSubMenu;
		int pos = y;

		//const char *zStr = element->Attribute("posZ", &z);
		if (z != -1)
		{
			HMENU hSubMenu3 = ::GetSubMenu(hSubMenu2, z);
			if (!hSubMenu3)
				continue;
			hMenu = hSubMenu2;
			pos = z;
		}
#ifdef UNICODE

		const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
		::ModifyMenu(hMenu, pos, MF_BYPOSITION, 0, nameW);
#else
		::ModifyMenu(hMenu, pos, MF_BYPOSITION, 0, name);
#endif
	}
}

int tabContextMenuItemPos[] = {
0, // 0 : Close 
1, // 1 : Close ALL BUT This
2, // 2 : Save
3, // 3 : Save As
7, // 4 : Print
16,// 5 : Move to Other View
17,// 6 : Clone to Other View
12,// 7 : Full File Path to Clipboard
13,// 8 : Filename to Clipboard
14,// 9 : Current Dir. Path to Clipboard
4, // 10: Rename
5, // 11: Delete
9, // 12: Read-Only
10,// 13: Clear Read-Only Flag
18,// 14: Move to New Instance
19,// 15: Open to New Instance
6, // 16: Reload

-1 //-------End
};

void NativeLangSpeaker::changeLangTabContextMenu(HMENU hCM)
{
	if (_nativeLangA)
	{
		TiXmlNodeA *tabBarMenu = _nativeLangA->FirstChild("Menu");
		if (tabBarMenu) 
		{
			tabBarMenu = tabBarMenu->FirstChild("TabBar");
			if (tabBarMenu)
			{
				WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
				int nbCMItems = sizeof(tabContextMenuItemPos)/sizeof(int);

				for (TiXmlNodeA *childNode = tabBarMenu->FirstChildElement("Item");
					childNode ;
					childNode = childNode->NextSibling("Item") )
				{
					TiXmlElementA *element = childNode->ToElement();
					int index;
					const char *indexStr = element->Attribute("CMID", &index);
					if (!indexStr || (index < 0 || index >= nbCMItems-1))
						continue;

					int pos = tabContextMenuItemPos[index];
					const char *pName = element->Attribute("name");
					if (pName)
					{
						const wchar_t *pNameW = wmc->char2wchar(pName, _nativeLangEncoding);
						int cmdID = ::GetMenuItemID(hCM, pos);
						::ModifyMenu(hCM, pos, MF_BYPOSITION, cmdID, pNameW);
					}
				}
			}
		}
	}
}

void NativeLangSpeaker::changeLangTabDrapContextMenu(HMENU hCM)
{
	const int POS_GO2VIEW = 0;
	const int POS_CLONE2VIEW = 1;
	const char *goToViewA = NULL;
	const char *cloneToViewA = NULL;

	if (_nativeLangA)
	{
		TiXmlNodeA *tabBarMenu = _nativeLangA->FirstChild("Menu");
		if (tabBarMenu)
			tabBarMenu = tabBarMenu->FirstChild("TabBar");
		if (tabBarMenu)
		{
			for (TiXmlNodeA *childNode = tabBarMenu->FirstChildElement("Item");
				childNode ;
				childNode = childNode->NextSibling("Item") )
			{
				TiXmlElementA *element = childNode->ToElement();
				int ordre;
				element->Attribute("CMID", &ordre);
				if (ordre == 5)
					goToViewA = element->Attribute("name");
				else if (ordre == 6)
					cloneToViewA = element->Attribute("name");
			}
		}
		//HMENU hCM = _tabPopupDropMenu.getMenuHandle();
#ifdef UNICODE
		WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
		if (goToViewA && goToViewA[0])
		{
			const wchar_t *goToViewG = wmc->char2wchar(goToViewA, _nativeLangEncoding);
			int cmdID = ::GetMenuItemID(hCM, POS_GO2VIEW);
			::ModifyMenu(hCM, POS_GO2VIEW, MF_BYPOSITION|MF_STRING, cmdID, goToViewG);
		}
		if (cloneToViewA && cloneToViewA[0])
		{
			const wchar_t *cloneToViewG = wmc->char2wchar(cloneToViewA, _nativeLangEncoding);
			int cmdID = ::GetMenuItemID(hCM, POS_CLONE2VIEW);
			::ModifyMenu(hCM, POS_CLONE2VIEW, MF_BYPOSITION|MF_STRING, cmdID, cloneToViewG);
		}
#else
		if (goToViewA && goToViewA[0])
		{
			int cmdID = ::GetMenuItemID(hCM, POS_GO2VIEW);
			::ModifyMenu(hCM, POS_GO2VIEW, MF_BYPOSITION, cmdID, goToViewA);
		}
		if (cloneToViewA && cloneToViewA[0])
		{
			int cmdID = ::GetMenuItemID(hCM, POS_CLONE2VIEW);
			::ModifyMenu(hCM, POS_CLONE2VIEW, MF_BYPOSITION, cmdID, cloneToViewA);
		}
#endif
	}
}

void NativeLangSpeaker::changeConfigLang(HWND hDlg)
{
	if (!_nativeLangA) return;

	TiXmlNodeA *styleConfDlgNode = _nativeLangA->FirstChild("Dialog");
	if (!styleConfDlgNode) return;	
	
	styleConfDlgNode = styleConfDlgNode->FirstChild("StyleConfig");
	if (!styleConfDlgNode) return;

	//HWND hDlg = _configStyleDlg.getHSelf();

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	// Set Title
	const char *titre = (styleConfDlgNode->ToElement())->Attribute("title");

	if ((titre && titre[0]) && hDlg)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		::SetWindowText(hDlg, nameW);
#else
		::SetWindowText(hDlg, titre);
#endif
	}
	for (TiXmlNodeA *childNode = styleConfDlgNode->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		const char *sentinel = element->Attribute("id", &id);
		const char *name = element->Attribute("name");
		if (sentinel && (name && name[0]))
		{
			HWND hItem = ::GetDlgItem(hDlg, id);
			if (hItem)
			{
#ifdef UNICODE
				const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
				::SetWindowText(hItem, nameW);
#else
				::SetWindowText(hItem, name);
#endif
			}
		}
	}
	styleConfDlgNode = styleConfDlgNode->FirstChild("SubDialog");
	
	for (TiXmlNodeA *childNode = styleConfDlgNode->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		const char *sentinel = element->Attribute("id", &id);
		const char *name = element->Attribute("name");
		if (sentinel && (name && name[0]))
		{
			HWND hItem = ::GetDlgItem(hDlg, id);
			if (hItem)
			{
#ifdef UNICODE
				const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
				::SetWindowText(hItem, nameW);
#else
				::SetWindowText(hItem, name);
#endif
			}
		}
	}
}


void NativeLangSpeaker::changeStyleCtrlsLang(HWND hDlg, int *idArray, const char **translatedText)
{
	const int iColorStyle = 0;
	const int iUnderline = 8;

	HWND hItem;
	for (int i = iColorStyle ; i < (iUnderline + 1) ; i++)
	{
		if (translatedText[i] && translatedText[i][0])
		{
			hItem = ::GetDlgItem(hDlg, idArray[i]);
			if (hItem)
			{
#ifdef UNICODE
				WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
				const wchar_t *nameW = wmc->char2wchar(translatedText[i], _nativeLangEncoding);
				::SetWindowText(hItem, nameW);
#else
				::SetWindowText(hItem, translatedText[i]);
#endif
				
			}
		}
	}
}

void NativeLangSpeaker::changeUserDefineLang(UserDefineDialog *userDefineDlg)
{
	if (!_nativeLangA) return;

	TiXmlNodeA *userDefineDlgNode = _nativeLangA->FirstChild("Dialog");
	if (!userDefineDlgNode) return;	
	
	userDefineDlgNode = userDefineDlgNode->FirstChild("UserDefine");
	if (!userDefineDlgNode) return;

	//UserDefineDialog *userDefineDlg = _pEditView->getUserDefineDlg();

	HWND hDlg = userDefineDlg->getHSelf();
#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	// Set Title
	const char *titre = (userDefineDlgNode->ToElement())->Attribute("title");
	if (titre && titre[0])
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		::SetWindowText(hDlg, nameW);
#else
		::SetWindowText(hDlg, titre);
#endif
	}
	// pour ses propres controls 	
	const int nbControl = 9;
	const char *translatedText[nbControl];
	for (int i = 0 ; i < nbControl ; i++)
		translatedText[i] = NULL;

	for (TiXmlNodeA *childNode = userDefineDlgNode->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		const char *sentinel = element->Attribute("id", &id);
		const char *name = element->Attribute("name");
		
		if (sentinel && (name && name[0]))
		{
			if (id > 30)
			{
				HWND hItem = ::GetDlgItem(hDlg, id);
				if (hItem)
				{
#ifdef UNICODE
					const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
					::SetWindowText(hItem, nameW);
#else
					::SetWindowText(hItem, name);
#endif
				}
			}
			else
			{
				switch(id)
				{
					case 0: case 1: case 2: case 3: case 4:
					case 5: case 6: case 7: case 8: 
 						translatedText[id] = name; break;
				}
			}
		}
	}

	const int nbDlg = 4;
	HWND hDlgArrary[nbDlg];
	hDlgArrary[0] = userDefineDlg->getFolderHandle();
	hDlgArrary[1] = userDefineDlg->getKeywordsHandle();
	hDlgArrary[2] = userDefineDlg->getCommentHandle();
	hDlgArrary[3] = userDefineDlg->getSymbolHandle();
	
	const int nbGrpFolder = 3;
	int folderID[nbGrpFolder][nbControl] = {
		//{IDC_DEFAULT_COLORSTYLEGROUP_STATIC, IDC_DEFAULT_FG_STATIC, IDC_DEFAULT_BG_STATIC, IDC_DEFAULT_FONTSTYLEGROUP_STATIC, IDC_DEFAULT_FONTNAME_STATIC, IDC_DEFAULT_FONTSIZE_STATIC, IDC_DEFAULT_BOLD_CHECK, IDC_DEFAULT_ITALIC_CHECK, IDC_DEFAULT_UNDERLINE_CHECK},\
		//{IDC_FOLDEROPEN_COLORSTYLEGROUP_STATIC, IDC_FOLDEROPEN_FG_STATIC, IDC_FOLDEROPEN_BG_STATIC, IDC_FOLDEROPEN_FONTSTYLEGROUP_STATIC, IDC_FOLDEROPEN_FONTNAME_STATIC, IDC_FOLDEROPEN_FONTSIZE_STATIC, IDC_FOLDEROPEN_BOLD_CHECK, IDC_FOLDEROPEN_ITALIC_CHECK, IDC_FOLDEROPEN_UNDERLINE_CHECK},\
		//{IDC_FOLDERCLOSE_COLORSTYLEGROUP_STATIC, IDC_FOLDERCLOSE_FG_STATIC, IDC_FOLDERCLOSE_BG_STATIC, IDC_FOLDERCLOSE_FONTSTYLEGROUP_STATIC, IDC_FOLDERCLOSE_FONTNAME_STATIC, IDC_FOLDERCLOSE_FONTSIZE_STATIC, IDC_FOLDERCLOSE_BOLD_CHECK, IDC_FOLDERCLOSE_ITALIC_CHECK, IDC_FOLDERCLOSE_UNDERLINE_CHECK}
	};

	const int nbGrpKeywords = 4;
	int keywordsID[nbGrpKeywords][nbControl] = {//\
		//{IDC_KEYWORD1_COLORSTYLEGROUP_STATIC, IDC_KEYWORD1_FG_STATIC, IDC_KEYWORD1_BG_STATIC, IDC_KEYWORD1_FONTSTYLEGROUP_STATIC, IDC_KEYWORD1_FONTNAME_STATIC, IDC_KEYWORD1_FONTSIZE_STATIC, IDC_KEYWORD1_BOLD_CHECK, IDC_KEYWORD1_ITALIC_CHECK, IDC_KEYWORD1_UNDERLINE_CHECK},\
		//{IDC_KEYWORD2_COLORSTYLEGROUP_STATIC, IDC_KEYWORD2_FG_STATIC, IDC_KEYWORD2_BG_STATIC, IDC_KEYWORD2_FONTSTYLEGROUP_STATIC, IDC_KEYWORD2_FONTNAME_STATIC, IDC_KEYWORD2_FONTSIZE_STATIC, IDC_KEYWORD2_BOLD_CHECK, IDC_KEYWORD2_ITALIC_CHECK, IDC_KEYWORD2_UNDERLINE_CHECK},\
		//{IDC_KEYWORD3_COLORSTYLEGROUP_STATIC, IDC_KEYWORD3_FG_STATIC, IDC_KEYWORD3_BG_STATIC, IDC_KEYWORD3_FONTSTYLEGROUP_STATIC, IDC_KEYWORD3_FONTNAME_STATIC, IDC_KEYWORD3_FONTSIZE_STATIC, IDC_KEYWORD3_BOLD_CHECK, IDC_KEYWORD3_ITALIC_CHECK, IDC_KEYWORD3_UNDERLINE_CHECK},\
		//{IDC_KEYWORD4_COLORSTYLEGROUP_STATIC, IDC_KEYWORD4_FG_STATIC, IDC_KEYWORD4_BG_STATIC, IDC_KEYWORD4_FONTSTYLEGROUP_STATIC, IDC_KEYWORD4_FONTNAME_STATIC, IDC_KEYWORD4_FONTSIZE_STATIC, IDC_KEYWORD4_BOLD_CHECK, IDC_KEYWORD4_ITALIC_CHECK, IDC_KEYWORD4_UNDERLINE_CHECK}
	};

	const int nbGrpComment = 3;
	int commentID[nbGrpComment][nbControl] = {//\
		//{IDC_COMMENT_COLORSTYLEGROUP_STATIC, IDC_COMMENT_FG_STATIC, IDC_COMMENT_BG_STATIC, IDC_COMMENT_FONTSTYLEGROUP_STATIC, IDC_COMMENT_FONTNAME_STATIC, IDC_COMMENT_FONTSIZE_STATIC, IDC_COMMENT_BOLD_CHECK, IDC_COMMENT_ITALIC_CHECK, IDC_COMMENT_UNDERLINE_CHECK},\
		//{IDC_NUMBER_COLORSTYLEGROUP_STATIC, IDC_NUMBER_FG_STATIC, IDC_NUMBER_BG_STATIC, IDC_NUMBER_FONTSTYLEGROUP_STATIC, IDC_NUMBER_FONTNAME_STATIC, IDC_NUMBER_FONTSIZE_STATIC, IDC_NUMBER_BOLD_CHECK, IDC_NUMBER_ITALIC_CHECK, IDC_NUMBER_UNDERLINE_CHECK},\
		//{IDC_COMMENTLINE_COLORSTYLEGROUP_STATIC, IDC_COMMENTLINE_FG_STATIC, IDC_COMMENTLINE_BG_STATIC, IDC_COMMENTLINE_FONTSTYLEGROUP_STATIC, IDC_COMMENTLINE_FONTNAME_STATIC, IDC_COMMENTLINE_FONTSIZE_STATIC, IDC_COMMENTLINE_BOLD_CHECK, IDC_COMMENTLINE_ITALIC_CHECK, IDC_COMMENTLINE_UNDERLINE_CHECK}
	};

	const int nbGrpOperator = 4;
	int operatorID[nbGrpOperator][nbControl] = {//\
		//{IDC_OPERATOR_COLORSTYLEGROUP_STATIC,   IDC_OPERATOR_FG_STATIC,   IDC_OPERATOR_BG_STATIC,   IDC_OPERATOR_FONTSTYLEGROUP_STATIC,   IDC_OPERATOR_FONTNAME_STATIC,   IDC_OPERATOR_FONTSIZE_STATIC,   IDC_OPERATOR_BOLD_CHECK,   IDC_OPERATOR_ITALIC_CHECK,   IDC_OPERATOR_UNDERLINE_CHECK},\
		//{IDC_DELIMITER1_COLORSTYLEGROUP_STATIC, IDC_DELIMITER1_FG_STATIC, IDC_DELIMITER1_BG_STATIC, IDC_DELIMITER1_FONTSTYLEGROUP_STATIC, IDC_DELIMITER1_FONTNAME_STATIC, IDC_DELIMITER1_FONTSIZE_STATIC, IDC_DELIMITER1_BOLD_CHECK, IDC_DELIMITER1_ITALIC_CHECK, IDC_DELIMITER1_UNDERLINE_CHECK},\
		//{IDC_DELIMITER2_COLORSTYLEGROUP_STATIC, IDC_DELIMITER2_FG_STATIC, IDC_DELIMITER2_BG_STATIC, IDC_DELIMITER2_FONTSTYLEGROUP_STATIC, IDC_DELIMITER2_FONTNAME_STATIC, IDC_DELIMITER2_FONTSIZE_STATIC, IDC_DELIMITER2_BOLD_CHECK, IDC_DELIMITER2_ITALIC_CHECK, IDC_DELIMITER2_UNDERLINE_CHECK},\
		//{IDC_DELIMITER3_COLORSTYLEGROUP_STATIC, IDC_DELIMITER3_FG_STATIC, IDC_DELIMITER3_BG_STATIC, IDC_DELIMITER3_FONTSTYLEGROUP_STATIC, IDC_DELIMITER3_FONTNAME_STATIC, IDC_DELIMITER3_FONTSIZE_STATIC, IDC_DELIMITER3_BOLD_CHECK, IDC_DELIMITER3_ITALIC_CHECK, IDC_DELIMITER3_UNDERLINE_CHECK}
	};

	int nbGpArray[nbDlg] = {nbGrpFolder, nbGrpKeywords, nbGrpComment, nbGrpOperator};
	const char nodeNameArray[nbDlg][16] = {"Folder", "Keywords", "Comment", "Operator"};

	for (int i = 0 ; i < nbDlg ; i++)
	{
	
		for (int j = 0 ; j < nbGpArray[i] ; j++)
		{
			switch (i)
			{
				case 0 : changeStyleCtrlsLang(hDlgArrary[i], folderID[j], translatedText); break;
				case 1 : changeStyleCtrlsLang(hDlgArrary[i], keywordsID[j], translatedText); break;
				case 2 : changeStyleCtrlsLang(hDlgArrary[i], commentID[j], translatedText); break;
				case 3 : changeStyleCtrlsLang(hDlgArrary[i], operatorID[j], translatedText); break;
			}
		}
		TiXmlNodeA *node = userDefineDlgNode->FirstChild(nodeNameArray[i]);
		
		if (node) 
		{
			// Set Title
			titre = (node->ToElement())->Attribute("title");
			if (titre &&titre[0])
			{
#ifdef UNICODE
				const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
				userDefineDlg->setTabName(i, nameW);
#else
				userDefineDlg->setTabName(i, titre);
#endif
			}
			for (TiXmlNodeA *childNode = node->FirstChildElement("Item");
				childNode ;
				childNode = childNode->NextSibling("Item") )
			{
				TiXmlElementA *element = childNode->ToElement();
				int id;
				const char *sentinel = element->Attribute("id", &id);
				const char *name = element->Attribute("name");
				if (sentinel && (name && name[0]))
				{
					HWND hItem = ::GetDlgItem(hDlgArrary[i], id);
					if (hItem)
					{
#ifdef UNICODE
						const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
						::SetWindowText(hItem, nameW);
#else
						::SetWindowText(hItem, name);
#endif
					}
				}
			}
		}
	}
}

void NativeLangSpeaker::changeFindReplaceDlgLang(FindReplaceDlg & findReplaceDlg)
{
	if (_nativeLangA)
	{
		TiXmlNodeA *dlgNode = _nativeLangA->FirstChild("Dialog");
		if (dlgNode)
		{
			NppParameters *pNppParam = NppParameters::getInstance();
			dlgNode = searchDlgNode(dlgNode, "Find");
			if (dlgNode)
			{
				const char *titre1 = (dlgNode->ToElement())->Attribute("titleFind");
				const char *titre2 = (dlgNode->ToElement())->Attribute("titleReplace");
				const char *titre3 = (dlgNode->ToElement())->Attribute("titleFindInFiles");
				const char *titre4 = (dlgNode->ToElement())->Attribute("titleMark");
#ifdef UNICODE
				WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();

				if (titre1 && titre1[0])
				{
					basic_string<wchar_t> nameW = wmc->char2wchar(titre1, _nativeLangEncoding);
					pNppParam->getFindDlgTabTitiles()._find = nameW;
					findReplaceDlg.changeTabName(FIND_DLG, pNppParam->getFindDlgTabTitiles()._find.c_str());
				}
				if (titre2  && titre2[0])
				{
					basic_string<wchar_t> nameW = wmc->char2wchar(titre2, _nativeLangEncoding);
					pNppParam->getFindDlgTabTitiles()._replace = nameW;
					findReplaceDlg.changeTabName(REPLACE_DLG, pNppParam->getFindDlgTabTitiles()._replace.c_str());
				}
				if (titre3 && titre3[0])
				{
					basic_string<wchar_t> nameW = wmc->char2wchar(titre3, _nativeLangEncoding);
					pNppParam->getFindDlgTabTitiles()._findInFiles = nameW;
					findReplaceDlg.changeTabName(FINDINFILES_DLG, pNppParam->getFindDlgTabTitiles()._findInFiles.c_str());
				}
				if (titre4 && titre4[0])
				{
					basic_string<wchar_t> nameW = wmc->char2wchar(titre4, _nativeLangEncoding);
					pNppParam->getFindDlgTabTitiles()._mark = nameW;
					findReplaceDlg.changeTabName(MARK_DLG, pNppParam->getFindDlgTabTitiles()._mark.c_str());
				}
#else
				if (titre1 && titre1[0])
				{
					pNppParam->getFindDlgTabTitiles()._find = titre1;
					findReplaceDlg.changeTabName(FIND_DLG, pNppParam->getFindDlgTabTitiles()._find.c_str());
				}
				if (titre2 && titre2[0])
				{
					pNppParam->getFindDlgTabTitiles()._replace = titre2;
					findReplaceDlg.changeTabName(REPLACE_DLG, pNppParam->getFindDlgTabTitiles()._replace.c_str());
				}
				if (titre3 && titre3[0])
				{
					pNppParam->getFindDlgTabTitiles()._findInFiles = titre3;
					findReplaceDlg.changeTabName(FINDINFILES_DLG, pNppParam->getFindDlgTabTitiles()._findInFiles.c_str());
				}
				if (titre4 && titre4[0])
				{
					pNppParam->getFindDlgTabTitiles()._mark = titre4;
					findReplaceDlg.changeTabName(MARK_DLG, pNppParam->getFindDlgTabTitiles()._mark.c_str());
				}
#endif
			}
		}
	}
	changeDlgLang(findReplaceDlg.getHSelf(), "Find");
}

void NativeLangSpeaker::changePrefereceDlgLang(PreferenceDlg & preference) 
{
	changeDlgLang(preference.getHSelf(), "Preference");

	char titre[128];

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	changeDlgLang(preference._barsDlg.getHSelf(), "Global", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("Global"), nameW);
#else
		preference._ctrlTab.renameTab("Global", titre);
#endif
	}
	changeDlgLang(preference._marginsDlg.getHSelf(), "Scintillas", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("Scintillas"), nameW);
#else
		preference._ctrlTab.renameTab("Scintillas", titre);
#endif
	}

	changeDlgLang(preference._defaultNewDocDlg.getHSelf(), "NewDoc", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("NewDoc"), nameW);
#else
		preference._ctrlTab.renameTab("NewDoc", titre);
#endif
	}

	changeDlgLang(preference._fileAssocDlg.getHSelf(), "FileAssoc", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("FileAssoc"), nameW);
#else
		preference._ctrlTab.renameTab("FileAssoc", titre);
#endif
	}

	changeDlgLang(preference._langMenuDlg.getHSelf(), "LangMenu", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("LangMenu"), nameW);
#else
		preference._ctrlTab.renameTab("LangMenu", titre);
#endif
	}

	changeDlgLang(preference._printSettingsDlg.getHSelf(), "Print", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("Print"), nameW);
#else
		preference._ctrlTab.renameTab("Print", titre);
#endif
	}
	changeDlgLang(preference._settingsDlg.getHSelf(), "MISC", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("MISC"), nameW);
#else
		preference._ctrlTab.renameTab("MISC", titre);
#endif
	}
	changeDlgLang(preference._backupDlg.getHSelf(), "Backup", titre);
	if (*titre)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		preference._ctrlTab.renameTab(TEXT("Backup"), nameW);
#else
		preference._ctrlTab.renameTab("Backup", titre);
#endif
	}
}

void NativeLangSpeaker::changeShortcutLang()
{
	if (!_nativeLangA) return;

	NppParameters * pNppParam = NppParameters::getInstance();
	vector<CommandShortcut> & mainshortcuts = pNppParam->getUserShortcuts();
	vector<ScintillaKeyMap> & scinshortcuts = pNppParam->getScintillaKeyList();
	int mainSize = (int)mainshortcuts.size();
	int scinSize = (int)scinshortcuts.size();

	TiXmlNodeA *shortcuts = _nativeLangA->FirstChild("Shortcuts");
	if (!shortcuts) return;

	shortcuts = shortcuts->FirstChild("Main");
	if (!shortcuts) return;

	TiXmlNodeA *entriesRoot = shortcuts->FirstChild("Entries");
	if (!entriesRoot) return;

	for (TiXmlNodeA *childNode = entriesRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int index, id;
		if (element->Attribute("index", &index) && element->Attribute("id", &id))
		{
			if (index > -1 && index < mainSize) { //valid index only
				const char *name = element->Attribute("name");
				CommandShortcut & csc = mainshortcuts[index];
				if (csc.getID() == (unsigned long)id) 
				{
#ifdef UNICODE
					WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
					const wchar_t * nameW = wmc->char2wchar(name, _nativeLangEncoding);
					csc.setName(nameW);
#else
					csc.setName(name);
#endif
				}
			}
		}
	}

	//Scintilla
	shortcuts = _nativeLangA->FirstChild("Shortcuts");
	if (!shortcuts) return;

	shortcuts = shortcuts->FirstChild("Scintilla");
	if (!shortcuts) return;

	entriesRoot = shortcuts->FirstChild("Entries");
	if (!entriesRoot) return;

	for (TiXmlNodeA *childNode = entriesRoot->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int index;
		if (element->Attribute("index", &index))
		{
			if (index > -1 && index < scinSize) { //valid index only
				const char *name = element->Attribute("name");
				ScintillaKeyMap & skm = scinshortcuts[index];
#ifdef UNICODE
				WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
				const wchar_t * nameW = wmc->char2wchar(name, _nativeLangEncoding);
				skm.setName(nameW);
#else
				skm.setName(name);
#endif
			}
		}
	}

}

void NativeLangSpeaker::changeShortcutmapperLang(ShortcutMapper * sm)
{
	if (!_nativeLangA) return;

	TiXmlNodeA *shortcuts = _nativeLangA->FirstChild("Dialog");
	if (!shortcuts) return;

	shortcuts = shortcuts->FirstChild("ShortcutMapper");
	if (!shortcuts) return;

	for (TiXmlNodeA *childNode = shortcuts->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int index;
		if (element->Attribute("index", &index))
		{
			if (index > -1 && index < 5)  //valid index only
			{
				const char *name = element->Attribute("name");

#ifdef UNICODE
				WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
				const wchar_t * nameW = wmc->char2wchar(name, _nativeLangEncoding);
				sm->translateTab(index, nameW);
#else
				sm->translateTab(index, name);
#endif
			}
		}
	}
}


TiXmlNodeA * NativeLangSpeaker::searchDlgNode(TiXmlNodeA *node, const char *dlgTagName)
{
	TiXmlNodeA *dlgNode = node->FirstChild(dlgTagName);
	if (dlgNode) return dlgNode;
	for (TiXmlNodeA *childNode = node->FirstChildElement();
		childNode ;
		childNode = childNode->NextSibling() )
	{
		dlgNode = searchDlgNode(childNode, dlgTagName);
		if (dlgNode) return dlgNode;
	}
	return NULL;
}

bool NativeLangSpeaker::changeDlgLang(HWND hDlg, const char *dlgTagName, char *title)
{
	if (title)
		title[0] = '\0';

	if (!_nativeLangA) return false;

	TiXmlNodeA *dlgNode = _nativeLangA->FirstChild("Dialog");
	if (!dlgNode) return false;

	dlgNode = searchDlgNode(dlgNode, dlgTagName);
	if (!dlgNode) return false;

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	// Set Title
	const char *titre = (dlgNode->ToElement())->Attribute("title");
	if ((titre && titre[0]) && hDlg)
	{
#ifdef UNICODE
		const wchar_t *nameW = wmc->char2wchar(titre, _nativeLangEncoding);
		::SetWindowText(hDlg, nameW);
#else
		::SetWindowText(hDlg, titre);
#endif
		if (title)
			strcpy(title, titre);
	}

	// Set the text of child control
	for (TiXmlNodeA *childNode = dlgNode->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		const char *sentinel = element->Attribute("id", &id);
		const char *name = element->Attribute("name");
		if (sentinel && (name && name[0]))
		{
			HWND hItem = ::GetDlgItem(hDlg, id);
			if (hItem)
			{
#ifdef UNICODE
				const wchar_t *nameW = wmc->char2wchar(name, _nativeLangEncoding);
				::SetWindowText(hItem, nameW);
#else
				::SetWindowText(hItem, name);
#endif
			}
		}
	}
	return true;
}

bool NativeLangSpeaker::getMsgBoxLang(const char *msgBoxTagName, generic_string & title, generic_string & message)
{
	title = TEXT("");
	message = TEXT("");

	if (!_nativeLangA) return false;

	TiXmlNodeA *msgBoxNode = _nativeLangA->FirstChild("MessageBox");
	if (!msgBoxNode) return false;

	msgBoxNode = searchDlgNode(msgBoxNode, msgBoxTagName);
	if (!msgBoxNode) return false;

#ifdef UNICODE
	WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
#endif

	// Set Title
	const char *titre = (msgBoxNode->ToElement())->Attribute("title");
	const char *msg = (msgBoxNode->ToElement())->Attribute("message");
	if ((titre && titre[0]) && (msg && msg[0]))
	{
#ifdef UNICODE
		title = wmc->char2wchar(titre, _nativeLangEncoding);
		message = wmc->char2wchar(msg, _nativeLangEncoding);
#else
		title = titre;
		message = msg;
#endif
		return true;
	}
	return false;
}

generic_string NativeLangSpeaker::getProjectPanelLangMenuStr(const char * nodeName, int cmdID, const TCHAR *defaultStr) const
{
	if (!_nativeLangA) return defaultStr;

	TiXmlNodeA *targetNode = _nativeLangA->FirstChild("ProjectManager");
	if (!targetNode) return defaultStr;

	targetNode = targetNode->FirstChild("Menus");
	if (!targetNode) return defaultStr;

	targetNode = targetNode->FirstChild(nodeName);
	if (!targetNode) return defaultStr;

	const char *name = NULL;
	for (TiXmlNodeA *childNode = targetNode->FirstChildElement("Item");
		childNode ;
		childNode = childNode->NextSibling("Item") )
	{
		TiXmlElementA *element = childNode->ToElement();
		int id;
		const char *idStr = element->Attribute("id", &id);

		if (idStr && id == cmdID)
		{
			name = element->Attribute("name");
			break;
		}
	}

	if (name && name[0])
	{
#ifdef UNICODE
		WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
		return wmc->char2wchar(name, _nativeLangEncoding);
#else
		return name;
#endif
	}
	return defaultStr;
}

generic_string NativeLangSpeaker::getProjectPanelLangStr(const char *nodeName, const TCHAR *defaultStr) const
{
	if (!_nativeLangA) return defaultStr;

	TiXmlNodeA *targetNode = _nativeLangA->FirstChild("ProjectManager");
	if (!targetNode) return defaultStr;
	targetNode = targetNode->FirstChild(nodeName);
	if (!targetNode) return defaultStr;

	// Set Title
	const char *name = (targetNode->ToElement())->Attribute("name");
	if (name && name[0])
	{
#ifdef UNICODE
		WcharMbcsConvertor *wmc = WcharMbcsConvertor::getInstance();
		return wmc->char2wchar(name, _nativeLangEncoding);
#else
		return name;
#endif
	}
	return defaultStr;
}

int NativeLangSpeaker::messageBox(const char *msgBoxTagName, HWND hWnd, TCHAR *defaultMessage, TCHAR *defaultTitle, int msgBoxType, int intInfo, TCHAR *strInfo)
{
	generic_string msg, title;
	size_t index;
	TCHAR int2Write[256];
	TCHAR intPlaceHolderSymbol[] = TEXT("$INT_REPLACE$");
	TCHAR strPlaceHolderSymbol[] = TEXT("$STR_REPLACE$");

	size_t intPlaceHolderLen = lstrlen(intPlaceHolderSymbol);
	size_t strPlaceHolderLen = lstrlen(strPlaceHolderSymbol);

	generic_sprintf(int2Write, TEXT("%d"), intInfo);

	if (!getMsgBoxLang(msgBoxTagName, title, msg))
	{
		title = defaultTitle;
		msg = defaultMessage;
	}
	index = title.find(intPlaceHolderSymbol);
	if (index != string::npos)
		title.replace(index, intPlaceHolderLen, int2Write);

	index = msg.find(intPlaceHolderSymbol);
	if (index != string::npos)
		msg.replace(index, intPlaceHolderLen, int2Write);

	if (strInfo)
	{
		index = title.find(strPlaceHolderSymbol);
		if (index != string::npos)
			title.replace(index, strPlaceHolderLen, strInfo);

		index = msg.find(strPlaceHolderSymbol);
		if (index != string::npos)
			msg.replace(index, strPlaceHolderLen, strInfo);
	}
	return ::MessageBox(hWnd, msg.c_str(), title.c_str(), msgBoxType);

	/*
	defaultTitle.replace(index, len, int2Write);
	defaultTitle.replace(index, len, str2Write);
	defaultMessage.replace(index, len, int2Write);
	defaultMessage.replace(index, len, str2Write);
	return ::MessageBox(hWnd, defaultMessage, defaultTitle, msgBoxType);
	*/
}