//this file is part of notepad++
//Copyright (C)2003 Don HO ( donho@altern.org )
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU General Public License
//as published by the Free Software Foundation; either
//version 2 of the License, or (at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You should have received a copy of the GNU General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

#include "precompiledHeaders.h"
#include "ControlsTab.h"

void ControlsTab::createTabs(WindowVector & winVector)
{
	_pWinVector = &winVector;

	for (int i = 0 ; i < int(winVector.size()) ; i++)
		TabBar::insertAtEnd(winVector[i]._name.c_str());

	TabBar::activateAt(0);
	activateWindowAt(0);
}

void ControlsTab::activateWindowAt(int index)
{
    if (index == _current)  return;
	(*_pWinVector)[_current]._dlg->display(false);
	(*_pWinVector)[index]._dlg->display(true);
	_current = index;
}

void ControlsTab::reSizeTo(RECT & rc)
{
	TabBar::reSizeTo(rc);
	rc.left += marge;
	rc.top += marge;
	
	//-- We do those dirty things 
	//-- because it's a "vertical" tab control
    if (_isVertical)
    {
	    rc.right -= 40;
	    rc.bottom -= 20;
	    if (getRowCount() == 2)
	    {
		    rc.right -= 20;
	    }
    }
	//-- end of dirty things
	rc.bottom -= 55;
	rc.right -= 20;

	(*_pWinVector)[_current]._dlg->reSizeTo(rc);
	(*_pWinVector)[_current]._dlg->redraw();

}

bool ControlsTab::renameTab(const TCHAR *internalName, const TCHAR *newName)
{
	bool foundIt = false;
	size_t i = 0;
	for ( ; i < _pWinVector->size() ; i++)
	{
		if ((*_pWinVector)[i]._internalName == internalName)
		{
			foundIt = true;
			break;
		}
	}
	if (!foundIt)
		return false;

	renameTab(i, newName);
	return true;
}

void ControlsTab::renameTab(int index, const TCHAR *newName)
{
	TCITEM tie;
	tie.mask = TCIF_TEXT;
	tie.pszText = (TCHAR *)newName;
	TabCtrl_SetItem(_hSelf, index, &tie);
}