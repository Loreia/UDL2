/*
this file is part of notepad++
Copyright (C)2003 Don HO <donho@altern.org>

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

#ifndef CONTEXTMENU
#define CONTEXTMENU

using namespace std;

struct MenuItemUnit {
	unsigned long _cmdID;
	generic_string _itemName;
	generic_string _parentFolderName;
	MenuItemUnit() : _cmdID(0), _itemName(TEXT("")), _parentFolderName(TEXT("")){};
	MenuItemUnit(unsigned long cmdID, generic_string itemName, generic_string parentFolderName=TEXT(""))
		: _cmdID(cmdID), _itemName(itemName), _parentFolderName(parentFolderName){};
	MenuItemUnit(unsigned long cmdID, const TCHAR *itemName, const TCHAR *parentFolderName=NULL);
};

class ContextMenu {
public:
	ContextMenu() : _hParent(NULL), _hMenu(NULL) {};
	~ContextMenu();

	void create(HWND hParent, const vector<MenuItemUnit> & menuItemArray);
	bool isCreated() const {return _hMenu != NULL;};
	
	void display(const POINT & p) const {
		::TrackPopupMenu(_hMenu, TPM_LEFTALIGN, p.x, p.y, 0, _hParent, NULL);
	};

	void enableItem(int cmdID, bool doEnable) const {
		int flag = doEnable?MF_ENABLED | MF_BYCOMMAND:MF_DISABLED | MF_GRAYED | MF_BYCOMMAND;
		::EnableMenuItem(_hMenu, cmdID, flag);
	};

	void checkItem(int cmdID, bool doCheck) const {
		::CheckMenuItem(_hMenu, cmdID, MF_BYCOMMAND | (doCheck?MF_CHECKED:MF_UNCHECKED));
	};

	HMENU getMenuHandle() {
		return _hMenu;
	};

private:
	HWND _hParent;
	HMENU _hMenu;
	vector<HMENU> _subMenus;

};

#endif //CONTEXTMENU
