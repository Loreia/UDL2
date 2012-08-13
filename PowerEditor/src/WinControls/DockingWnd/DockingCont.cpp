//this file is part of docking functionality for Notepad++
//Copyright (C)2006 Jens Lorenz <jens.plugin.npp@gmx.de>
//
//This program is free software; you can redistribute it and/or
//modify it under the terms of the GNU General Public License
//as published by the Free Software Foundation; either
//version 2 of the License, or (at your option) any later version.
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
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You should have received a copy of the GNU General Public License
//along with this program; if not, write to the Free Software
//Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

#include "precompiledHeaders.h"
#include "dockingResource.h"
#include "DockingCont.h"

#include "SplitterContainer.h"
#include "ToolTip.h"
#include "Parameters.h"

#ifndef WH_MOUSE_LL
#define WH_MOUSE_LL 14
#endif

static HWND		hWndServer		= NULL;
static HHOOK	hookMouse		= NULL;

static LRESULT CALLBACK hookProcMouse(UINT nCode, WPARAM wParam, LPARAM lParam)
{
    if(nCode < 0)
    {
		::CallNextHookEx(hookMouse, nCode, wParam, lParam);
        return 0;
    }

    switch (wParam)
    {
		case WM_MOUSEMOVE:
		case WM_NCMOUSEMOVE:
			::PostMessage(hWndServer, wParam, 0, 0);
			break;
		case WM_LBUTTONUP:
		case WM_NCLBUTTONUP:
			::PostMessage(hWndServer, wParam, 0, 0);
			break;
        default: 
			break;
	}

	return ::CallNextHookEx(hookMouse, nCode, wParam, lParam);
}


DockingCont::DockingCont()
{
	_isMouseOver		= FALSE;
	_isMouseClose		= FALSE;
	_isMouseDown		= FALSE;
	_isFloating			= false;
	_isTopCaption		= CAPTION_TOP;
	_dragFromTab		= FALSE;
	_hContTab			= NULL;
	_hDefaultTabProc	= NULL;
	_beginDrag			= FALSE;
	_prevItem			= 0;
	_hFont				= NULL;
	_bTabTTHover		= FALSE;
	_bCaptionTT			= FALSE;
	_bCapTTHover		= FALSE;
	_hoverMPos			= posClose;
	_bDrawOgLine		= TRUE;
	_vTbData.clear();
}

DockingCont::~DockingCont()
{
	::DeleteObject(_hFont);
}


void DockingCont::doDialog(bool willBeShown, bool isFloating)
{
	if (!isCreated())
	{
		create(IDD_CONTAINER_DLG);

		_isFloating  = isFloating;

		if (_isFloating)
		{
			::SetWindowLongPtr(_hSelf, GWL_STYLE, POPUP_STYLES);
			::SetWindowLongPtr(_hSelf, GWL_EXSTYLE, POPUP_EXSTYLES);
			::ShowWindow(_hCaption, SW_HIDE);
		}
		else
		{
			::SetWindowLongPtr(_hSelf, GWL_STYLE, CHILD_STYLES);
			::SetWindowLongPtr(_hSelf, GWL_EXSTYLE, CHILD_EXSTYLES);
			::ShowWindow(_hCaption, SW_SHOW);
		}

		//If you want defualt GUI font
		_hFont = (HFONT)GetStockObject(DEFAULT_GUI_FONT);
	}

	display(willBeShown);
}


tTbData* DockingCont::createToolbar(tTbData data)
{
	tTbData *pTbData = new tTbData;

	*pTbData = data;

	// force window style of client window
	::SetWindowLongPtr(pTbData->hClient, GWL_STYLE, CHILD_STYLES);
	::SetWindowLongPtr(pTbData->hClient, GWL_EXSTYLE, CHILD_EXSTYLES);

	// restore position if plugin is in floating state
	if ((_isFloating) && (::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0) == 0))
	{
		reSizeToWH(pTbData->rcFloat);
	}

	// set attached child window
    ::SetParent(pTbData->hClient, ::GetDlgItem(_hSelf, IDC_CLIENT_TAB));

	// set names for captions and view toolbar
	viewToolbar(pTbData);

	// attach to list
	_vTbData.push_back(pTbData);

	return pTbData;
}


void DockingCont::removeToolbar(tTbData TbData)
{
	// remove from list
	for (size_t iTb = 0; iTb < _vTbData.size(); iTb++)
	{
		if (_vTbData[iTb]->hClient == TbData.hClient)
		{
			// remove tab
			removeTab(_vTbData[iTb]);

			// free resources
			delete _vTbData[iTb];
			vector<tTbData*>::iterator itr = _vTbData.begin() + iTb;
			_vTbData.erase(itr);
		}
	}
}


tTbData* DockingCont::findToolbarByWnd(HWND hClient)
{
	tTbData*	pTbData		= NULL;

	// find entry by handle
	for (size_t iTb = 0; iTb < _vTbData.size(); iTb++)
	{
		if (hClient == _vTbData[iTb]->hClient)
		{
			pTbData = _vTbData[iTb];
		}
	}
	return pTbData;
}

tTbData* DockingCont::findToolbarByName(TCHAR* pszName)
{
	tTbData*	pTbData		= NULL;

	// find entry by handle
	for (size_t iTb = 0; iTb < _vTbData.size(); iTb++)
	{
		if (lstrcmp(pszName, _vTbData[iTb]->pszName) == 0)
		{
			pTbData = _vTbData[iTb];
		}
	}
	return pTbData;
}

void DockingCont::setActiveTb(tTbData* pTbData)
{
	int iItem = SearchPosInTab(pTbData);
	setActiveTb(iItem);
}

void DockingCont::setActiveTb(int iItem)
{
	//if ((iItem != -1) && (iItem < ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0)))
	if (iItem < ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0))
	{
		SelectTab(iItem);
	}
}

int DockingCont::getActiveTb()
{
	return ::SendMessage(_hContTab, TCM_GETCURSEL, 0, 0);
}

tTbData* DockingCont::getDataOfActiveTb()
{
	tTbData*	pTbData	= NULL;
	int			iItem	= getActiveTb();

	if (iItem != -1)
	{
		TCITEM	tcItem	= {0};

		tcItem.mask		= TCIF_PARAM;
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
		pTbData = (tTbData*)tcItem.lParam;
	}

	return pTbData;
}

vector<tTbData*> DockingCont::getDataOfVisTb()
{
	vector<tTbData*>	vTbData;
	TCITEM				tcItem		= {0};
	int					iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

	tcItem.mask	= TCIF_PARAM;

	for(int iItem = 0; iItem < iItemCnt; iItem++)
	{
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
		vTbData.push_back((tTbData*)tcItem.lParam);
	}
	return vTbData;
}

bool DockingCont::isTbVis(tTbData* data)
{
	TCITEM				tcItem		= {0};
	int					iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

	tcItem.mask	= TCIF_PARAM;

	for(int iItem = 0; iItem < iItemCnt; iItem++)
	{
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
		if (!tcItem.lParam)
			return false;
		if (((tTbData*)tcItem.lParam) == data)
			return true;
	}
	return false;
}


//
//    Process function of caption bar
//
LRESULT DockingCont::runProcCaption(HWND hwnd, UINT Message, WPARAM wParam, LPARAM lParam)
{
	static ToolTip	toolTip;

	switch (Message)
	{
		case WM_LBUTTONDOWN:
		{
			_isMouseDown = TRUE;

			if (isInRect(hwnd, LOWORD(lParam), HIWORD(lParam)) == posClose)
			{
				_isMouseClose	= TRUE;
				_isMouseOver	= TRUE;

				// start hooking
				hWndServer		= _hCaption;
				winVer ver = (NppParameters::getInstance())->getWinVersion();
				hookMouse	= ::SetWindowsHookEx(ver >= WV_W2K?WH_MOUSE_LL:WH_MOUSE, (HOOKPROC)hookProcMouse, _hInst, 0);

				if (!hookMouse)
				{
					DWORD dwError = ::GetLastError();
					TCHAR  str[128];
					::wsprintf(str, TEXT("GetLastError() returned %lu"), dwError);
					::MessageBox(NULL, str, TEXT("SetWindowsHookEx(MOUSE) failed"), MB_OK | MB_ICONERROR);
				}
				::RedrawWindow(hwnd, NULL, NULL, TRUE);
			}

			focusClient();
			return TRUE;
		}
		case WM_LBUTTONUP:
		{
			_isMouseDown = FALSE;
			if (_isMouseClose == TRUE)
			{
				// end hooking
				::UnhookWindowsHookEx(hookMouse);

				if (_isMouseOver == TRUE)
				{
					doClose();
				}
				_isMouseClose	= FALSE;
				_isMouseOver	= FALSE;
			}
			
			focusClient();
			return TRUE;
		}
		case WM_LBUTTONDBLCLK:
		{
			if (isInRect(hwnd, LOWORD(lParam), HIWORD(lParam)) == posCaption)
				::SendMessage(_hParent, DMM_FLOATALL, 0, (LPARAM)this);

			focusClient();
			return TRUE;
		}
		case WM_MOUSEMOVE:
		{
			POINT	pt			= {0};

			// get correct cursor position
			::GetCursorPos(&pt);
			::ScreenToClient(_hCaption, &pt);

			if (_isMouseDown == TRUE)
			{
				if (_isMouseClose == FALSE)
				{
                    // keep sure that button is still down and within caption
                    if ((wParam == MK_LBUTTON) && (isInRect(hwnd, pt.x, pt.y) == posCaption))
                    {
    					_dragFromTab = FALSE;
    					NotifyParent(DMM_MOVE);
    					_isMouseDown = FALSE;
                    }
                    else
                    {
                        _isMouseDown = FALSE;
                    }
				}
				else
				{
					BOOL    isMouseOver	= _isMouseOver;
					_isMouseOver = (isInRect(hwnd, pt.x, pt.y) == posClose ? TRUE : FALSE);

					// if state is changed draw new
					if (_isMouseOver != isMouseOver)
					{
						::SetFocus(NULL);
						::RedrawWindow(hwnd, NULL, NULL, TRUE);
					}
				}
			}
			else if (_bCapTTHover == FALSE)
			{
				_hoverMPos = isInRect(hwnd, LOWORD(lParam), HIWORD(lParam));

				if ((_bCaptionTT == TRUE) || (_hoverMPos == posClose))
				{
					TRACKMOUSEEVENT tme;
					tme.cbSize = sizeof(tme);
					tme.hwndTrack = hwnd;
					tme.dwFlags = TME_LEAVE | TME_HOVER;
					tme.dwHoverTime = 1000;
					_bCapTTHover = _TrackMouseEvent(&tme);
				}
			}
			else if ((_bCapTTHover == TRUE) &&
				(_hoverMPos != isInRect(hwnd, LOWORD(lParam), HIWORD(lParam))))
			{
				toolTip.destroy();
				_bCapTTHover = FALSE;
			}
			return TRUE;
		}
		case WM_MOUSEHOVER:
		{
			RECT	rc	= {0};
			POINT	pt	= {0};


			// get mouse position
			::GetCursorPos(&pt);

			toolTip.init(_hInst, hwnd);
			if (_hoverMPos == posCaption)
			{
				toolTip.Show(rc, _pszCaption.c_str(), pt.x, pt.y + 20);
			}
			else
			{
				toolTip.Show(rc, TEXT("Close"), pt.x, pt.y + 20);
			}
			return TRUE;
		}
		case WM_MOUSELEAVE:
		{
			toolTip.destroy();
			_bCapTTHover = FALSE;
			return TRUE;
		}
		case WM_SIZE:
		{
			::GetWindowRect(hwnd, &_rcCaption);
			ScreenRectToClientRect(hwnd, &_rcCaption);
			break;
		}
		case WM_SETTEXT:
		{
			::RedrawWindow(hwnd, NULL, NULL, TRUE);
			return TRUE;
		}
		default:
			break;
	}

	return ::CallWindowProc(_hDefaultCaptionProc, hwnd, Message, wParam, lParam);
}

void DockingCont::drawCaptionItem(DRAWITEMSTRUCT *pDrawItemStruct)
{
	HBRUSH		bgbrush		= NULL;
	HFONT		hOldFont	= NULL;
	RECT		rc			= pDrawItemStruct->rcItem;
	HDC			hDc			= pDrawItemStruct->hDC;
	HPEN		hPen		= ::CreatePen(PS_SOLID, 1, ::GetSysColor(COLOR_BTNSHADOW));
	BITMAP		bmp			= {0};
	HBITMAP		hBmpCur		= NULL;
	HBITMAP		hBmpOld 	= NULL;
	HBITMAP		hBmpNew		= NULL;
	UINT		length  	= _pszCaption.length();

	int nSavedDC			= ::SaveDC(hDc);

	// begin with paint
	::SetBkMode(hDc, TRANSPARENT);

	if (_isActive == TRUE) {
		bgbrush = ::CreateSolidBrush(::GetSysColor(COLOR_ACTIVECAPTION));
		::SetTextColor(hDc, ::GetSysColor(COLOR_CAPTIONTEXT));
	} else {
		bgbrush = ::CreateSolidBrush(::GetSysColor(COLOR_BTNFACE));
	}

	// set text and/or caption grid
	if (_isTopCaption == TRUE)
	{
		if (_isActive == TRUE)
		{
			// fill background
			::FillRect(hDc, &rc, bgbrush);
			rc.right	-= 1;
			rc.bottom	-= 1;
		}
		else
		{
			// fill background
			rc.right	-= 1;
			rc.bottom	-= 1;
			::FillRect(hDc, &rc, bgbrush);

			// draw grid lines

			MoveToEx(hDc, rc.left , rc.top , NULL);
			LineTo  (hDc, rc.right, rc.top );
			LineTo  (hDc, rc.right, rc.bottom );
			LineTo  (hDc, rc.left , rc.bottom );
			LineTo  (hDc, rc.left , rc.top);
		}

		// draw text
		rc.left		+= 2;
		rc.top		+= 1;
		rc.right	-= 16;
		hOldFont = (HFONT)::SelectObject(hDc, _hFont);
		::DrawText(hDc, _pszCaption.c_str(), length, &rc, DT_LEFT | DT_SINGLELINE | DT_VCENTER | DT_END_ELLIPSIS | DT_NOPREFIX);

		// calculate text size and if its trankated...
		SIZE	size	= {0};
		GetTextExtentPoint32(hDc, _pszCaption.c_str(), length, &size);
		_bCaptionTT = (((rc.right - rc.left) < size.cx) ? TRUE : FALSE);

		::SelectObject(hDc, hOldFont);
	}
	else
	{
		// create local font for vertical draw
		HFONT	hFont;

		if (_isActive == TRUE)
		{
			// fill background
			::FillRect(hDc, &rc, bgbrush);
			rc.right	-= 1;
			rc.bottom	-= 1;
		}
		else
		{
			// fill background
			rc.right	-= 1;
			rc.bottom	-= 1;
			::FillRect(hDc, &rc, bgbrush);

			// draw grid lines
			MoveToEx(hDc, rc.left , rc.top , NULL);
			LineTo  (hDc, rc.right, rc.top );
			LineTo  (hDc, rc.right, rc.bottom );
			LineTo  (hDc, rc.left , rc.bottom );
			LineTo  (hDc, rc.left , rc.top);
		}

		// draw text
		rc.left		+= 1;
		rc.top		+= HIGH_CAPTION;
		// to make ellipsis working
		rc.right	= rc.bottom - rc.top;
		rc.bottom	+= 14;

		hFont = ::CreateFont(12, 0, 90 * 10, 0,
			 FW_NORMAL, FALSE, FALSE, FALSE,
			 ANSI_CHARSET, OUT_DEFAULT_PRECIS,
			 CLIP_DEFAULT_PRECIS, DEFAULT_QUALITY,
			 DEFAULT_PITCH | FF_ROMAN,
			 TEXT("MS Shell Dlg"));

		hOldFont = (HFONT)::SelectObject(hDc, hFont);
		::DrawText(hDc, _pszCaption.c_str(), length, &rc, DT_BOTTOM | DT_SINGLELINE | DT_END_ELLIPSIS | DT_NOPREFIX);

		// calculate text size and if its trankated...
		SIZE	size	= {0};
		GetTextExtentPoint32(hDc, _pszCaption.c_str(), length, &size);
		_bCaptionTT = (((rc.bottom - rc.top) < size.cy) ? TRUE : FALSE);

		::SelectObject(hDc, hOldFont);
		::DeleteObject(hFont);
	}
	::DeleteObject(hPen);
	::DeleteObject(bgbrush);

	// draw button
	HDC			dcMem		= ::CreateCompatibleDC(NULL);

	// select correct bitmap
	if ((_isMouseOver == TRUE) && (_isMouseDown == TRUE))
		hBmpCur = ::LoadBitmap(_hInst, MAKEINTRESOURCE(IDB_CLOSE_DOWN));
	else
		hBmpCur = ::LoadBitmap(_hInst, MAKEINTRESOURCE(IDB_CLOSE_UP));

	// blit bitmap into the destination
	::GetObject(hBmpCur, sizeof(bmp), &bmp);
	hBmpOld = (HBITMAP)::SelectObject(dcMem, hBmpCur);
	hBmpNew = ::CreateCompatibleBitmap(dcMem, bmp.bmWidth, bmp.bmHeight);

	rc = pDrawItemStruct->rcItem;
	::SelectObject(hDc, hBmpNew);

	if (_isTopCaption == TRUE)
		::BitBlt(hDc, rc.right-bmp.bmWidth-CLOSEBTN_POS_LEFT, CLOSEBTN_POS_TOP, bmp.bmWidth, bmp.bmHeight, dcMem, 0, 0, SRCCOPY);
	else
		::BitBlt(hDc, CLOSEBTN_POS_LEFT, CLOSEBTN_POS_LEFT, bmp.bmWidth, bmp.bmHeight, dcMem, 0, 0, SRCCOPY);

	::SelectObject(dcMem, hBmpOld);
	::DeleteObject(hBmpCur);
	::DeleteObject(hBmpNew);
	::DeleteDC(dcMem);

	::RestoreDC(hDc, nSavedDC);
}

eMousePos DockingCont::isInRect(HWND hwnd, int x, int y)
{
	RECT		rc;
	eMousePos	ret	= posOutside;

	::GetWindowRect(hwnd, &rc);
	ScreenRectToClientRect(hwnd, &rc);

	if (_isTopCaption == TRUE)
	{
		if ((x > rc.left) && (x < rc.right-HIGH_CAPTION) && (y > rc.top) && (y < rc.bottom))
		{
			ret = posCaption;
		}
		else if ((x > rc.right-(12+CLOSEBTN_POS_LEFT)) && (x < (rc.right-CLOSEBTN_POS_LEFT)) && 
			(y > (rc.top+CLOSEBTN_POS_TOP)) && (y < (rc.bottom-CLOSEBTN_POS_TOP)))
		{
			ret = posClose;
		}
	}
	else
	{
		if ((x > rc.left) && (x < rc.right) && (y > rc.top+HIGH_CAPTION) && (y < rc.bottom))
		{
			ret = posCaption;
		}
		else if ((x > rc.left+CLOSEBTN_POS_LEFT) && (x < rc.right-CLOSEBTN_POS_LEFT) && 
			(y > (rc.top+CLOSEBTN_POS_TOP)) && (y < (rc.top+(12+CLOSEBTN_POS_LEFT))))
		{
			ret = posClose;
		}
	}

	return ret;
}


//----------------------------------------------------------
//    Process function of tab
//
LRESULT DockingCont::runProcTab(HWND hwnd, UINT Message, WPARAM wParam, LPARAM lParam)
{
	static	ToolTip	toolTip;

	switch (Message)
	{
		case WM_LBUTTONDOWN:
		{
			_beginDrag	= TRUE;
			return TRUE;
		}
		case WM_LBUTTONUP:
		{
			int				iItem	= 0;
			TCHITTESTINFO	info	= {0};

			// get selected sub item
			info.pt.x = LOWORD(lParam);
			info.pt.y = HIWORD(lParam);
			iItem = ::SendMessage(hwnd, TCM_HITTEST, 0, (LPARAM)&info);

			SelectTab(iItem);
			_beginDrag = FALSE;
			return TRUE;
		}
		case WM_LBUTTONDBLCLK:
		{
			NotifyParent((_isFloating == true)?DMM_DOCK:DMM_FLOAT);
			return TRUE;
		}
		case WM_MBUTTONUP:
		{
			int				iItem	= 0;
			TCITEM			tcItem	= {0};
			TCHITTESTINFO	info	= {0};

			// get selected sub item
			info.pt.x = LOWORD(lParam);
			info.pt.y = HIWORD(lParam);
			iItem = ::SendMessage(hwnd, TCM_HITTEST, 0, (LPARAM)&info);

			SelectTab(iItem);

			// get data and hide toolbar
			tcItem.mask		= TCIF_PARAM;
			::SendMessage(hwnd, TCM_GETITEM, iItem, (LPARAM)&tcItem);

			if (!tcItem.lParam)
				return FALSE;

			// notify child windows
			if (NotifyParent(DMM_CLOSE) == 0)
			{
				hideToolbar((tTbData*)tcItem.lParam);
			}
			return TRUE;
		}

		case WM_MOUSEMOVE:
		{
			int				iItem	= 0;
			TCHITTESTINFO	info	= {0};

			// get selected sub item
			info.pt.x = LOWORD(lParam);
			info.pt.y = HIWORD(lParam);
			iItem = ::SendMessage(hwnd, TCM_HITTEST, 0, (LPARAM)&info);

			if ((_beginDrag == TRUE) && (wParam == MK_LBUTTON))
			{
				SelectTab(iItem);

				// send moving message to parent window
				_dragFromTab = TRUE;
				NotifyParent(DMM_MOVE);
				_beginDrag = FALSE;
			}
            else
            {
				int	iItemSel = ::SendMessage(hwnd, TCM_GETCURSEL, 0, 0);

				if ((_bTabTTHover == FALSE) && (iItem != iItemSel))
				{
					TRACKMOUSEEVENT tme;
					tme.cbSize = sizeof(tme);
					tme.hwndTrack = hwnd;
					tme.dwFlags = TME_LEAVE | TME_HOVER;
					tme.dwHoverTime = 1000;
					_bTabTTHover = _TrackMouseEvent(&tme);
				}
				else
				{
					if (iItem == iItemSel)
					{
						toolTip.destroy();
						_bTabTTHover = FALSE;
					}
					else if (iItem != _iLastHovered)
					{
						TCITEM	tcItem	= {0};
						RECT	rc		= {0};

						// destroy old tooltip
						toolTip.destroy();

						// recalc mouse position
						::ClientToScreen(hwnd, &info.pt);

						// get text of toolbar
						tcItem.mask		= TCIF_PARAM;
						::SendMessage(hwnd, TCM_GETITEM, iItem, (LPARAM)&tcItem);
						if (!tcItem.lParam)
							return FALSE;

						toolTip.init(_hInst, hwnd);
						toolTip.Show(rc, ((tTbData*)tcItem.lParam)->pszName, info.pt.x, info.pt.y + 20);
					}
				}

				// save last hovered item
				_iLastHovered = iItem;

				_beginDrag = FALSE;
			}
			return TRUE;
		}

		case WM_MOUSEHOVER:
		{
			int				iItem	= 0;
			TCITEM			tcItem	= {0};
			RECT			rc		= {0};
			TCHITTESTINFO	info	= {0};

			// get selected sub item
			info.pt.x = LOWORD(lParam);
			info.pt.y = HIWORD(lParam);
			iItem = ::SendMessage(hwnd, TCM_HITTEST, 0, (LPARAM)&info);

			// recalc mouse position
			::ClientToScreen(hwnd, &info.pt);

			// get text of toolbar
			tcItem.mask		= TCIF_PARAM;
			::SendMessage(hwnd, TCM_GETITEM, iItem, (LPARAM)&tcItem);
			if (!tcItem.lParam)
				return FALSE;

			toolTip.init(_hInst, hwnd);
			toolTip.Show(rc, ((tTbData*)tcItem.lParam)->pszName, info.pt.x, info.pt.y + 20);
			return TRUE;
		}

		case WM_MOUSELEAVE:
		{
			toolTip.destroy();
			_bTabTTHover = FALSE;
			return TRUE;
		}

		case WM_NOTIFY:
		{
			LPNMHDR	lpnmhdr = (LPNMHDR)lParam;

			if ((lpnmhdr->hwndFrom == _hContTab) && (lpnmhdr->code == TCN_GETOBJECT))
			{
				int				iItem	= 0;
				TCHITTESTINFO	info	= {0};

				// get selected sub item
				info.pt.x = LOWORD(lParam);
				info.pt.y = HIWORD(lParam);
				iItem = ::SendMessage(hwnd, TCM_HITTEST, 0, (LPARAM)&info);

				SelectTab(iItem);
			}
			break;
		}
		default:
			break;
	}

	return ::CallWindowProc(_hDefaultTabProc, hwnd, Message, wParam, lParam);
}

void DockingCont::drawTabItem(DRAWITEMSTRUCT *pDrawItemStruct)
{
	TCITEM	tcItem		= {0};
	RECT	rc			= pDrawItemStruct->rcItem;
	
	int		nTab		= pDrawItemStruct->itemID;
	bool	isSelected	= (nTab == getActiveTb());

	// get current selected item
	tcItem.mask = TCIF_PARAM;
	::SendMessage(_hContTab, TCM_GETITEM, nTab, (LPARAM)&tcItem);
	if (!tcItem.lParam)
		return;

	const TCHAR *text	= ((tTbData*)tcItem.lParam)->pszName;
	int		length	= lstrlen(((tTbData*)tcItem.lParam)->pszName);


	// get drawing context
	HDC hDc = pDrawItemStruct->hDC;

	int nSavedDC = ::SaveDC(hDc);

	// For some bizarre reason the rcItem you get extends above the actual
	// drawing area. We have to workaround this "feature".
	rc.top += ::GetSystemMetrics(SM_CYEDGE);

	::SetBkMode(hDc, TRANSPARENT);
	HBRUSH hBrush = ::CreateSolidBrush(::GetSysColor(COLOR_BTNFACE));
	::FillRect(hDc, &rc, hBrush);
	::DeleteObject((HGDIOBJ)hBrush);

	// draw orange bar
	if ((_bDrawOgLine == TRUE) && (isSelected))
	{
		RECT barRect  = rc;
		barRect.top  += rc.bottom - 4;

		hBrush = ::CreateSolidBrush(RGB(250, 170, 60));
		::FillRect(hDc, &barRect, hBrush);
		::DeleteObject((HGDIOBJ)hBrush);

	}

	// draw icon if enabled
	if (((tTbData*)tcItem.lParam)->uMask & DWS_ICONTAB)
	{
		HIMAGELIST	hImageList	= (HIMAGELIST)::SendMessage(_hParent, DMM_GETIMAGELIST, 0, 0);
		int			iPosImage	= ::SendMessage(_hParent, DMM_GETICONPOS, 0, (LPARAM)((tTbData*)tcItem.lParam)->hClient);

		if ((hImageList != NULL) && (iPosImage >= 0))
		{
			// Get height of image so we
			IMAGEINFO	info		= {0};
			RECT &		imageRect	= info.rcImage;
			
			ImageList_GetImageInfo(hImageList, iPosImage, &info);
			ImageList_Draw(hImageList, iPosImage, hDc, rc.left + 3, 2, ILD_NORMAL);

			if (isSelected == true)
			{
				rc.left += imageRect.right - imageRect.left + 5;
			}
		}
	}

	if (isSelected == true)
	{
		COLORREF _unselectedColor = RGB(0, 0, 0);
		::SetTextColor(hDc, _unselectedColor);

		// draw text
		rc.top -= ::GetSystemMetrics(SM_CYEDGE);
		::SelectObject(hDc, _hFont);
		::DrawText(hDc, text, length, &rc, DT_SINGLELINE | DT_VCENTER | DT_NOPREFIX);
	}

	::RestoreDC(hDc, nSavedDC);
}


//----------------------------------------------
//    Process function of dialog
//
BOOL CALLBACK DockingCont::run_dlgProc(UINT Message, WPARAM wParam, LPARAM lParam)
{
	switch (Message) 
	{
		case WM_NCACTIVATE:
		{
			// Note: lParam to identify the trigger window
			if ((int)lParam != -1)
			{
				::SendMessage(_hParent, WM_NCACTIVATE, wParam, 0);
			}
			break;
		}
		case WM_INITDIALOG:
		{
			_hContTab = ::GetDlgItem(_hSelf, IDC_TAB_CONT);
			_hCaption = ::GetDlgItem(_hSelf, IDC_BTN_CAPTION);

			// intial subclassing of caption
			::SetWindowLongPtr(_hCaption, GWLP_USERDATA, (LONG_PTR)this);
			_hDefaultCaptionProc = reinterpret_cast<WNDPROC>(::SetWindowLongPtr(_hCaption, GWLP_WNDPROC, (LONG_PTR)wndCaptionProc));

			// intial subclassing of tab
			::SetWindowLongPtr(_hContTab, GWLP_USERDATA, (LONG_PTR)this);
			_hDefaultTabProc = reinterpret_cast<WNDPROC>(::SetWindowLongPtr(_hContTab, GWLP_WNDPROC, (LONG_PTR)wndTabProc));

			// set min tab width
			::SendMessage(_hContTab, TCM_SETMINTABWIDTH, 0, (LPARAM)MIN_TABWIDTH);
			break;
		}
		case WM_NCCALCSIZE:
		case WM_SIZE:
		{
			onSize();
			break;
		}
		case WM_DRAWITEM :
		{
			// draw tab or caption
			if (((DRAWITEMSTRUCT *)lParam)->CtlID == IDC_TAB_CONT)
			{
				drawTabItem((DRAWITEMSTRUCT *)lParam);
				return TRUE;
			}
			else
			{
				drawCaptionItem((DRAWITEMSTRUCT *)lParam);
				return TRUE;
			}
			break;
		}
		case WM_NCLBUTTONDBLCLK :
		{
			RECT	rcWnd		= {0};
			RECT	rcClient	= {0};
			POINT	pt			= {HIWORD(lParam), LOWORD(lParam)};

			getWindowRect(rcWnd);
			getClientRect(rcClient);
			ClientRectToScreenRect(_hSelf, &rcClient);
			rcWnd.bottom = rcClient.top;

			// if in caption
			if ((rcWnd.top  < pt.x) && (rcWnd.bottom > pt.x) &&
				(rcWnd.left < pt.y) && (rcWnd.right  > pt.y))
			{
				NotifyParent(DMM_DOCKALL);
				return TRUE;
			}
			break;
		}
		case WM_SYSCOMMAND :
		{
			switch (wParam & 0xfff0)
			{
				case SC_MOVE:
					NotifyParent(DMM_MOVE);
					return TRUE;
				default: 
					break;
			}
			return FALSE;
		}
		case WM_COMMAND : 
		{
			switch (LOWORD(wParam))
			{   
				case IDCANCEL:
					doClose();
					return TRUE;
				default :
					break;
			}
			break;
		}
		default:
			break;
	}

	return FALSE;
}

void DockingCont::onSize()
{
	TCITEM	tcItem		= {0};
	RECT	rc			= {0};
	RECT	rcTemp		= {0};
	UINT	iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);
	UINT	iTabOff		= 0;

	getClientRect(rc);

	if (iItemCnt >= 1)
	{
		// resize to docked window
		if (_isFloating == false)
		{
			// draw caption
			if (_isTopCaption == TRUE)
			{
				::SetWindowPos(_hCaption, NULL, rc.left, rc.top, rc.right, HIGH_CAPTION, SWP_NOZORDER | SWP_NOACTIVATE);
				rc.top		+= HIGH_CAPTION;
				rc.bottom	-= HIGH_CAPTION;
			}
			else
			{
				::SetWindowPos(_hCaption, NULL, rc.left, rc.top, HIGH_CAPTION, rc.bottom, SWP_NOZORDER | SWP_NOACTIVATE);
				rc.left		+= HIGH_CAPTION;
				rc.right	-= HIGH_CAPTION;
			}

			if (iItemCnt >= 2)
			{
				// resize tab and plugin control if tabs exceeds one
				// resize tab
				rcTemp = rc;
				rcTemp.top		= (rcTemp.bottom + rcTemp.top) - (HIGH_TAB+CAPTION_GAP);
				rcTemp.bottom	= HIGH_TAB;
				iTabOff			= HIGH_TAB;

				::SetWindowPos(_hContTab, NULL,
								rcTemp.left, rcTemp.top, rcTemp.right, rcTemp.bottom, 
								SWP_NOZORDER | SWP_SHOWWINDOW |  SWP_NOACTIVATE);
			}

			// resize client area for plugin
			rcTemp = rc;
			if (_isTopCaption == TRUE)
			{
				rcTemp.top    += CAPTION_GAP;
				rcTemp.bottom -= (iTabOff + CAPTION_GAP);
			}
			else
			{
				rcTemp.left   += CAPTION_GAP;
				rcTemp.right  -= CAPTION_GAP;
				rcTemp.bottom -= iTabOff;
			}

			// set position of client area
			::SetWindowPos(::GetDlgItem(_hSelf, IDC_CLIENT_TAB), NULL,
							rcTemp.left, rcTemp.top, rcTemp.right, rcTemp.bottom, 
							SWP_NOZORDER | SWP_NOACTIVATE);
		}
		// resize to float window
		else
		{
			// update floating size
			if (_isFloating == true)
			{
				for (size_t iTb = 0; iTb < _vTbData.size(); iTb++)
				{
					getWindowRect(_vTbData[iTb]->rcFloat);
				}
			}			

			// draw caption
			if (iItemCnt >= 2)
			{
				// resize tab if size of elements exceeds one
				rcTemp = rc;
				rcTemp.top    = rcTemp.bottom - (HIGH_TAB+CAPTION_GAP);
				rcTemp.bottom = HIGH_TAB;

				::SetWindowPos(_hContTab, NULL,
								rcTemp.left, rcTemp.top, rcTemp.right, rcTemp.bottom, 
								SWP_NOZORDER | SWP_SHOWWINDOW);
			}

			// resize client area for plugin
			rcTemp = rc;
			rcTemp.bottom -= ((iItemCnt == 1)?0:HIGH_TAB);

			::SetWindowPos(::GetDlgItem(_hSelf, IDC_CLIENT_TAB), NULL,
							rcTemp.left, rcTemp.top, rcTemp.right, rcTemp.bottom, 
							SWP_NOZORDER | SWP_NOACTIVATE);
		}
		

		// get active item data
		UINT	iItemCnt = ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

		// resize visible plugin windows
		for (UINT iItem = 0; iItem < iItemCnt; iItem++)
		{
			tcItem.mask		= TCIF_PARAM;
			::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
			if (!tcItem.lParam)
				continue;

			::SetWindowPos(((tTbData*)tcItem.lParam)->hClient, NULL,
							0, 0, rcTemp.right, rcTemp.bottom, 
							SWP_NOZORDER);
			//::SendMessage(((tTbData*)tcItem.lParam)->hClient, WM_SIZE, 0, MAKELONG(rcTemp.right, rcTemp.bottom));
			// Notify switch in
			NMHDR nmhdr;
			nmhdr.code		= DMN_FLOATDROPPED;
			nmhdr.hwndFrom	= _hSelf;
			nmhdr.idFrom	= 0;
			::SendMessage(((tTbData*)tcItem.lParam)->hClient, WM_NOTIFY, nmhdr.idFrom, (LPARAM)&nmhdr);
			
		}
	}
}

void DockingCont::doClose()
{
	int	iItemOff	= 0;
	int	iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

	for (int iItem = 0; iItem < iItemCnt; iItem++)
	{
		TCITEM		tcItem		= {0};

		// get item data
		SelectTab(iItemOff);
		tcItem.mask	= TCIF_PARAM;
		::SendMessage(_hContTab, TCM_GETITEM, iItemOff, (LPARAM)&tcItem);
		if (!tcItem.lParam)
			continue;

		// notify child windows
		if (NotifyParent(DMM_CLOSE) == 0)
		{
			// delete tab
			hideToolbar((tTbData*)tcItem.lParam);
		}
		else
		{
			iItemOff++;
		}
	}

	if (iItemOff == 0)
	{
		// hide dialog first
		this->doDialog(false);
		::SendMessage(_hParent, WM_SIZE, 0, 0);
	}
}

void DockingCont::showToolbar(tTbData* pTbData, BOOL state)
{
	if (state == SW_SHOW)
	{
		viewToolbar(pTbData);
	}
	else
	{
		hideToolbar(pTbData);
	}
}

int DockingCont::hideToolbar(tTbData *pTbData, BOOL hideClient)
{
	int		iItem	= SearchPosInTab(pTbData);

	// delete item
	if (TRUE == ::SendMessage(_hContTab, TCM_DELETEITEM, iItem, 0))
	{
		UINT	iItemCnt = ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

		if (iItemCnt != 0)
		{
			TCITEM		tcItem = {0};

			tcItem.mask	= TCIF_PARAM;

			if ((unsigned int)iItem == iItemCnt)
			{
				iItem--;
			}

			// activate new selected item and view plugin dialog
			_prevItem = iItem;
			SelectTab(iItem);

			// hide tabs if only one element
			if (iItemCnt == 1)
			{
				::ShowWindow(_hContTab, SW_HIDE);
			}
		}
		else 
		{
			// hide dialog
			this->doDialog(false);

			// send message to docking manager for resize
			if (!_isFloating)
			{
				::SendMessage(_hParent, WM_SIZE, 0, 0);
			}
		}

		// keep sure, that client is hide!!!
		if (hideClient == TRUE)
		{
			::ShowWindow(pTbData->hClient, SW_HIDE);
		}
	}
	onSize();

	return iItem;
}

void DockingCont::viewToolbar(tTbData *pTbData)
{
	TCITEM		tcItem		= {0};
	int			iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

	if (iItemCnt > 0)
	{
		UINT	iItem	= getActiveTb();

		tcItem.mask		= TCIF_PARAM;
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
		if (!tcItem.lParam)
			return;
		
		// hide active dialog
		::ShowWindow(((tTbData*)tcItem.lParam)->hClient, SW_HIDE);
	}

	// create new tab if it not exists
	int iTabPos = SearchPosInTab(pTbData);
	tcItem.mask			= TCIF_PARAM;
	tcItem.lParam		= (LPARAM)pTbData;

	if (iTabPos == -1)
	{
		// set only params and text even if icon available
		::SendMessage(_hContTab, TCM_INSERTITEM, iItemCnt, (LPARAM)&tcItem);
		SelectTab(iItemCnt);
	}
	// if exists select it and update data
	else
	{
		::SendMessage(_hContTab, TCM_SETITEM, iTabPos, (LPARAM)&tcItem);
		SelectTab(iTabPos);
	}

	// show dialog and notify parent to update dialog view
	if (isVisible() == false)
	{
		this->doDialog();
		::SendMessage(_hParent, WM_SIZE, 0, 0);
	}

	// set position of client
	onSize();
}

int DockingCont::SearchPosInTab(tTbData* pTbData)
{
	TCITEM	tcItem		= {0};
	int		iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

	tcItem.mask	= TCIF_PARAM;

	for (int iItem = 0; iItem < iItemCnt; iItem++)
	{
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
		if (!tcItem.lParam)
			continue;

		if (((tTbData*)tcItem.lParam)->hClient == pTbData->hClient)
			return iItem;
	}
	return -1;
}

void DockingCont::SelectTab(int iTab)
{
	if (iTab != -1)
	{
		const TCHAR	*pszMaxTxt	= NULL;
		TCITEM	tcItem		= {0};
		SIZE	size		= {0};
		int		maxWidth	= 0;
		int		iItemCnt	= ::SendMessage(_hContTab, TCM_GETITEMCOUNT, 0, 0);

		// get data of new active dialog
		tcItem.mask		= TCIF_PARAM;
		::SendMessage(_hContTab, TCM_GETITEM, iTab, (LPARAM)&tcItem);
		// show active dialog
		if (!tcItem.lParam)
			return;

		::ShowWindow(((tTbData*)tcItem.lParam)->hClient, SW_SHOW);
		::SetFocus(((tTbData*)tcItem.lParam)->hClient);

		// Notify switch in
		NMHDR nmhdr;
		nmhdr.code		= DMN_SWITCHIN;
		nmhdr.hwndFrom	= _hSelf;
		nmhdr.idFrom	= 0;
		::SendMessage(((tTbData*)tcItem.lParam)->hClient, WM_NOTIFY, nmhdr.idFrom, (LPARAM)&nmhdr);

		if ((unsigned int)iTab != _prevItem)
		{
			// hide previous dialog
			::SendMessage(_hContTab, TCM_GETITEM, _prevItem, (LPARAM)&tcItem);

			if (!tcItem.lParam)
				return;
			::ShowWindow(((tTbData*)tcItem.lParam)->hClient, SW_HIDE);
		
			// Notify switch off
			NMHDR nmhdr;
			nmhdr.code		= DMN_SWITCHOFF;
			nmhdr.hwndFrom	= _hSelf;
			nmhdr.idFrom	= 0;
			::SendMessage(((tTbData*)tcItem.lParam)->hClient, WM_NOTIFY, nmhdr.idFrom, (LPARAM)&nmhdr);
		}

		// resize tab item

		// get at first largest item ...
		HDC		hDc	= ::GetDC(_hContTab);
		SelectObject(hDc, _hFont);

		for (int iItem = 0; iItem < iItemCnt; iItem++)
		{
			const TCHAR *pszTabTxt = NULL;

			::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);
			if (!tcItem.lParam)
				continue;
			pszTabTxt = ((tTbData*)tcItem.lParam)->pszName;

			// get current font width
			GetTextExtentPoint32(hDc, pszTabTxt, lstrlen(pszTabTxt), &size);

			if (maxWidth < size.cx) 
			{
				maxWidth	= size.cx;
				pszMaxTxt	= pszTabTxt;
			}
		}
		::ReleaseDC(_hSelf, hDc);

		tcItem.mask	= TCIF_TEXT;

		for (int iItem = 0; iItem < iItemCnt; iItem++)
		{
			generic_string szText(TEXT(""));
			if (iItem == iTab && pszMaxTxt)
			{
				// fake here an icon before text ...
				szText = TEXT("    ");
				szText += pszMaxTxt;
			}
			tcItem.pszText = (TCHAR *)szText.c_str();
			::SendMessage(_hContTab, TCM_SETITEM, iItem, (LPARAM)&tcItem);
		}

		// selects the pressed tab and store previous tab
		::SendMessage(_hContTab, TCM_SETCURSEL, iTab, 0);
		_prevItem = iTab;

		// update caption text
		updateCaption();

		onSize();
	}
}

bool DockingCont::updateCaption()
{
	if (!_hContTab)
		return false;

	TCITEM			tcItem	= {0};
	int				iItem	= getActiveTb();

	if (iItem < 0)
		return false;

	// get data of new active dialog
	tcItem.mask		= TCIF_PARAM;
	::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);

	if (!tcItem.lParam) return false;

	// update caption text
	_pszCaption = ((tTbData*)tcItem.lParam)->pszName;

	// test if additional information are available
	if ((((tTbData*)tcItem.lParam)->uMask & DWS_ADDINFO) && 
		(lstrlen(((tTbData*)tcItem.lParam)->pszAddInfo) != 0))
	{
		_pszCaption += TEXT(" - ");
		_pszCaption += ((tTbData*)tcItem.lParam)->pszAddInfo; 
	}

	if (_isFloating == true)
	{
		::SetWindowText(_hSelf, _pszCaption.c_str());
	}
	else
	{
		::SetWindowText(_hCaption, _pszCaption.c_str());
	}
	return true;
}

void DockingCont::focusClient()
{
	TCITEM		tcItem	= {0};
	int			iItem	= getActiveTb();	

	if (iItem != -1)
	{
		// get data of new active dialog
		tcItem.mask		= TCIF_PARAM;
		::SendMessage(_hContTab, TCM_GETITEM, iItem, (LPARAM)&tcItem);

		// set focus
		if (!tcItem.lParam)
			return;

		tTbData *tbData = (tTbData *)tcItem.lParam;
		if (tbData->pszAddInfo && lstrcmp(tbData->pszAddInfo, DM_NOFOCUSWHILECLICKINGCAPTION) == 0)
			return;
		
		::SetFocus(tbData->hClient);
	}
}

LPARAM DockingCont::NotifyParent(UINT message)
{
	return ::SendMessage(_hParent, message, 0, (LPARAM)this);
}

